#!/usr/bin/env python3
"""
Phase V-B / Workstream D (light part): cost estimate for level 7, independent recomputation of the pinned ground
state at levels 3-5 (FR30, unit-cube control, trivial-link control, random substitution decoration seed 108),
D_2 estimates in every level window with uncertainties, energy-resolved analysis at level 5, and tests of the four
competing explanations of the IPR*n growth.

Everything below is recomputed in this script except where a value is explicitly read from a stored artifact
(audit/results/phase5a_*; those are marked "stored" in the output).

Operator (same conventions as audit/phase5a_controls.py): l^2(tiles) x C^2, (A psi)_a = sum over shared unit panels
f=(a,b) of C_ab psi_b, C_ab = (sigma.M_a^T n_f)(sigma.M_b^T n_f) in Q8, C_ba = C_ab^dagger, panels between the same
tile pair summed with multiplicity; H = diag(d_a) I_2 - A.  Pinned: d_a = bulk coordination (24 chair, 6 cube);
free: d_a = deg_a; Robin(t): d_a = deg_a + t (bulk - deg_a).  Trivial-link control: links I_2, so the operator is
two copies of the tile operator bulk - A_0; we solve the real tile operator (dim n).
Geometry: OWN vectorised builder (pose recursion -> owner grid of unit cubes -> panels), depth-first tile order,
validated entry by entry against the object builders of phase5a_controls / independent_clifford_q8_audit.
Solvers: OWN code.  level <= 3 dense scipy.linalg.eigh (full spectrum); level 4 ARPACK shift-invert
(scipy eigsh, sigma below the bottom, sparse LU); level 5 OWN Chebyshev-filtered subspace iteration (Zhou-Saad
scaled filter + Rayleigh-Ritz on the exact operator) cross-checked at level 4 against shift-invert.
Residuals ||H psi - lambda psi||_2 are evaluated with the exact sparse operator for every reported eigenpair.

Usage (repository root, OMP_NUM_THREADS=1):
  python3 -u -I audit/phase5b_d_scaling.py cost                  # D1: matvec timing / memory at levels 5 and 6, level-7 extrapolation
  python3 -u -I audit/phase5b_d_scaling.py solve <system> <level> [K]   # systems: fr30 cube trivial randdec108 fr30_free fr30_robin50
  python3 -u -I audit/phase5b_d_scaling.py analyze               # D2 + D3 tables -> audit/results/phase5b_d_scaling.txt/.json
Per-stage outputs: audit/results/phase5b_d_cost.json, phase5b_d_solve_<system>_L<level>.json (+ .npz with the lowest-K tile densities).
"""
import os, sys, time, json, resource, itertools, collections
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
RES = os.path.join(HERE, 'results')
import numpy as np, scipy.sparse as sps, scipy.sparse.linalg as spl, scipy.linalg as sla
from independent_clifford_q8_audit import FR30, U3, perm_mat, tiles_at_level, panel_edges, clifford_link, q8label
from phase5a_scaling_controls import random_decoration

V8 = list(itertools.product((0, 1), repeat=3))
SIG = [np.array([[0, 1], [1, 0]], complex), np.array([[0, -1j], [1j, 0]], complex), np.array([[1, 0], [0, -1]], complex)]
Q8_NAMES = ['+1', '-1', '+i', '-i', '+j', '-j', '+k', '-k']
Q8_MATS = {'+1': np.eye(2, dtype=complex), '-1': -np.eye(2, dtype=complex)}
for k, nm in enumerate('ijk'):
    Q8_MATS['+' + nm] = 1j * SIG[k]; Q8_MATS['-' + nm] = -1j * SIG[k]
CUBE_DEC = {v: FR30.get(v, (0, 2, 1)) for v in V8}
TAG = 'phase5b_d'

def rss_gb(): return resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 1e6
def conv(o):
    if isinstance(o, np.integer): return int(o)
    if isinstance(o, np.floating): return float(o)
    if isinstance(o, np.ndarray): return o.tolist()
    if isinstance(o, (set, frozenset, tuple)): return list(o)
    raise TypeError(str(type(o)))
def jdump(obj, name):
    with open(os.path.join(RES, name), 'w') as f: json.dump(obj, f, indent=1, default=conv)
def jload(name):
    p = os.path.join(RES, name); return json.load(open(p)) if os.path.exists(p) else None
def say(msg=''): print(msg, flush=True)

# ============================================================================================ systems
SYSTEMS = {
    'fr30':         dict(kind='chair', dec=FR30, links='clifford', bulk=24, diag='pinned', title='FR30 chair / Clifford Q8, pinned 24'),
    'cube':         dict(kind='cube', dec=CUBE_DEC, links='clifford', bulk=6, diag='pinned', title='unit cube / FR30-type decoration / Clifford, pinned 6'),
    'trivial':      dict(kind='chair', dec=FR30, links='trivial', bulk=24, diag='pinned', title='FR30 chair graph / trivial links (tile operator 24 - A_0)'),
    'randdec108':   dict(kind='chair', dec=None, links='clifford', bulk=24, diag='pinned', title='chair / random admissible decoration seed 108 / Clifford, pinned 24'),
    'fr30_free':    dict(kind='chair', dec=FR30, links='clifford', bulk=24, diag='free', title='FR30 chair / Clifford Q8, free (diag = deg)'),
    'fr30_robin50': dict(kind='chair', dec=FR30, links='clifford', bulk=24, diag='robin', t=0.5, title='FR30 chair / Clifford Q8, Robin t=0.5 (diag = deg + 0.5 (24 - deg))'),
}
def decoration(system):
    s = SYSTEMS[system]
    if s['dec'] is None:
        dec, draws = random_decoration(int(system[7:])); return dec
    return s['dec']

# ============================================================================================ geometry (own vectorised builder)
def Ds(v): return np.diag([1 - 2 * v[0], 1 - 2 * v[1], 1 - 2 * v[2]])
def substitution(kind, dec):
    if kind == 'chair':
        opG = np.array([perm_mat(dec['0'])] + [Ds(v) @ perm_mat(dec[v]) for v in U3], dtype=np.int64)
        opT = np.array([[1, 1, 1]] + [[4 * v[0], 4 * v[1], 4 * v[2]] for v in U3], dtype=np.int64)
        base = np.array([[2 * u[0] + 1, 2 * u[1] + 1, 2 * u[2] + 1] for u in U3], dtype=np.int64)
        return opG, opT, base, (lambda L: 2 ** (L + 1))
    opG = np.array([Ds(v) @ perm_mat(dec[v]) for v in V8], dtype=np.int64)
    opT = np.array([[2 * v[0], 2 * v[1], 2 * v[2]] for v in V8], dtype=np.int64)
    return opG, opT, np.array([[1, 1, 1]], dtype=np.int64), (lambda L: 2 ** L)

def poses(opG, opT, level):
    """pose list identical to [(G@g, 2T+G@t) for (G,T) in poses for (g,t) in ops] (parent-major = depth-first)."""
    Gs = np.eye(3, dtype=np.int64)[None]; Ts = np.zeros((1, 3), dtype=np.int64)
    for _ in range(level):
        Gn = np.einsum('pij,ojk->poik', Gs, opG).reshape(-1, 3, 3)
        Tn = (2 * Ts[:, None, :] + np.einsum('pij,oj->poi', Gs, opT)).reshape(-1, 3)
        Gs, Ts = Gn, Tn
    return Gs, Ts

def own_link_label(Ma, Mb, ax):
    """Q8 label of C_ab = (sigma . M_a^T e_ax)(sigma . M_b^T e_ax), computed from the Pauli matrices."""
    n = np.zeros(3, dtype=np.int64); n[ax] = 1
    ua = Ma.T @ n; ub = Mb.T @ n
    C = sum(ua[j] * SIG[j] for j in range(3)) @ sum(ub[j] * SIG[j] for j in range(3))
    for nm, M in Q8_MATS.items():
        if np.allclose(C, M): return nm
    raise ValueError('link not in Q8')

def geometry(system, level):
    s = SYSTEMS[system]; dec = decoration(system); t0 = time.time()
    opG, opT, base, side = substitution(s['kind'], dec)
    G, T = poses(opG, opT, level); n = G.shape[0]; nb = base.shape[0]
    cubes = (np.einsum('pij,cj->pci', G, base) + 2 * T[:, None, :] - 1) // 2
    S = side(level); assert cubes.min() >= 0 and cubes.max() < S
    owner = np.full((S, S, S), -1, dtype=np.int32); flat = cubes.reshape(-1, 3)
    owner[flat[:, 0], flat[:, 1], flat[:, 2]] = np.repeat(np.arange(n, dtype=np.int32), nb)
    occ = owner >= 0; assert occ.sum() == nb * n, 'overlapping unit cubes'
    if s['kind'] == 'chair':
        h = S // 2; expect = np.ones((S, S, S), bool); expect[h:, h:, h:] = False; assert (occ == expect).all()
    else: assert occ.all()
    del cubes, flat, occ
    ea, eb, eax = [], [], []
    for ax in range(3):
        o1 = np.moveaxis(owner, ax, 0)[:-1]; o2 = np.moveaxis(owner, ax, 0)[1:]
        sel = (o1 >= 0) & (o2 >= 0) & (o1 != o2)
        ea.append(o1[sel].astype(np.int64)); eb.append(o2[sel].astype(np.int64)); eax.append(np.full(int(sel.sum()), ax, dtype=np.int64))
    del owner
    ea = np.concatenate(ea); eb = np.concatenate(eb); eax = np.concatenate(eax)
    keys, fid = np.unique(G.reshape(n, 9), axis=0, return_inverse=True); fid = fid.reshape(-1)
    frames = [k.reshape(3, 3) for k in keys]; F = len(frames)
    table = np.empty((F, F, 3), dtype=np.int64)
    for i in range(F):
        for j in range(F):
            for ax in range(3): table[i, j, ax] = Q8_NAMES.index(own_link_label(frames[i], frames[j], ax))
    lab = table[fid[ea], fid[eb], eax]
    deg = np.bincount(ea, minlength=n) + np.bincount(eb, minlength=n); assert deg.max() == s['bulk']
    return dict(system=system, level=level, n=n, ea=ea, eb=eb, eax=eax, lab=lab, deg=deg, bulk=s['bulk'], nframes=F,
                label_counts={Q8_NAMES[i]: int(c) for i, c in zip(*np.unique(lab, return_counts=True))}, build_s=time.time() - t0, G=G)

def diag_vector(system, geo):
    s = SYSTEMS[system]; deg = geo['deg'].astype(float); b = float(s['bulk'])
    if s['diag'] == 'pinned': return np.full(geo['n'], b)
    if s['diag'] == 'free': return deg
    return deg + s['t'] * (b - deg)

def build_H(system, geo, diag=None):
    """Sparse Hermitian H = diag I_2 - A (complex CSR, dim 2n); trivial links -> real tile operator diag - A_0 (dim n)."""
    n, ea, eb, lab = geo['n'], geo['ea'], geo['eb'], geo['lab']
    d = diag_vector(system, geo) if diag is None else diag
    if SYSTEMS[system]['links'] == 'trivial':
        A = sps.coo_matrix((np.ones(2 * len(ea)), (np.concatenate([ea, eb]), np.concatenate([eb, ea]))), shape=(n, n)).tocsr()
        return (sps.diags(d) - A).tocsr()
    rows = [np.arange(2 * n)]; cols = [np.arange(2 * n)]; vals = [np.repeat(d, 2).astype(complex)]
    for li, name in enumerate(Q8_NAMES):
        sel = np.nonzero(lab == li)[0]
        if len(sel) == 0: continue
        C = Q8_MATS[name]; a = ea[sel]; b = eb[sel]
        for r in range(2):
            for c in range(2):
                if C[r, c] != 0:
                    rows.append(2 * a + r); cols.append(2 * b + c); vals.append(np.full(len(sel), -C[r, c]))
                    rows.append(2 * b + c); cols.append(2 * a + r); vals.append(np.full(len(sel), -np.conj(C[r, c])))
    rows = np.concatenate(rows).astype(np.int32); cols = np.concatenate(cols).astype(np.int32); vals = np.concatenate(vals)
    H = sps.csr_matrix((vals, (rows, cols)), shape=(2 * n, 2 * n)); del rows, cols, vals
    H.sum_duplicates(); H.eliminate_zeros(); return H

def validate_against_objects(system, geo, H):
    """Entry-by-entry comparison with the object builders (tiles_at_level / cube_tiles + panel_edges + clifford_link + phase5a_controls.build_H)."""
    import phase5a_controls as pc
    s = SYSTEMS[system]; dec = decoration(system); t0 = time.time()
    tiles = tiles_at_level(dec, geo['level']) if s['kind'] == 'chair' else pc.cube_tiles(dec, geo['level'])
    owner, edges = panel_edges(tiles); n = len(tiles); assert n == geo['n']
    Gref = np.array([G for G, _, _ in tiles]); same_order = bool((Gref == geo['G']).all())
    links = [pc.I2] * len(edges) if s['links'] == 'trivial' else pc.clifford_links(tiles, edges)
    d = diag_vector(system, geo)
    if s['links'] == 'trivial':
        Href = pc.build_H(n, edges, links, d); Href = Href[0::2, 0::2]          # one spin copy of the trivial operator = tile operator
    else: Href = pc.build_H(n, edges, links, d)
    D = H - Href; dev = float(np.abs(D.data).max()) if D.nnz else 0.0
    degref = pc.degrees(n, edges)
    return dict(n_edges_ref=len(edges), n_edges=int(len(geo['ea'])), max_abs_dev=dev, degrees_identical=bool((degref == geo['deg']).all()),
                tile_order_identical=same_order, seconds=time.time() - t0)

def interface_masks(geo):
    """I_d = tiles incident to a panel whose two tiles lie in different depth-d children (child = index // 8^(L-d))."""
    L, n, ea, eb = geo['level'], geo['n'], geo['ea'], geo['eb']; out = {}
    for d in range(1, L + 1):
        q = 8 ** (L - d); cross = (ea // q) != (eb // q)
        m = np.zeros(n, dtype=bool); m[ea[cross]] = True; m[eb[cross]] = True; out[d] = m
    return out

def tile_adjacency(geo):
    n, ea, eb = geo['n'], geo['ea'], geo['eb']
    return sps.coo_matrix((np.ones(2 * len(ea)), (np.concatenate([ea, eb]), np.concatenate([eb, ea]))), shape=(n, n)).tocsr()

def graph_distance(adj, seed_mask):
    """BFS tile distance from a set of tiles."""
    n = adj.shape[0]; dist = np.full(n, -1, dtype=np.int64); front = np.nonzero(seed_mask)[0]; dist[front] = 0; d = 0
    while len(front):
        d += 1; nb = np.unique(adj[front].indices); nb = nb[dist[nb] < 0]; dist[nb] = d; front = nb
    return dist

# ============================================================================================ densities and statistics
def IPR(p): return float((p ** 2).sum())
def S2_profile(p, L):
    """S_2(d) = sum over the 8^d depth-d children (contiguous blocks in depth-first order) of (child weight)^2, d=0..L."""
    return [float((p.reshape(8 ** d, 8 ** (L - d)).sum(axis=1) ** 2).sum()) for d in range(L + 1)]
def Sq_profile(p, L, q): return [float((p.reshape(8 ** d, 8 ** (L - d)).sum(axis=1) ** q).sum()) for d in range(L + 1)]
def local_D2(S2): return [float(np.log2(S2[d - 1] / S2[d])) for d in range(1, len(S2))]
def tile_density(v, spinor):
    p = (np.abs(v[0::2]) ** 2 + np.abs(v[1::2]) ** 2) if spinor else np.abs(v) ** 2
    return p / p.sum()

def state_stats(p, geo, masks):
    L, n = geo['level'], geo['n']; ps = np.sort(p)[::-1]; cum = np.cumsum(ps)
    S2 = S2_profile(p, L); S3 = Sq_profile(p, L, 3)
    st = dict(ipr=IPR(p), ipr_n=IPR(p) * n, ipr3=float((p ** 3).sum()), ipr4=float((p ** 4).sum()), p_max=float(ps[0]),
              s50=int(np.searchsorted(cum, 0.5) + 1), s90=int(np.searchsorted(cum, 0.9) + 1),
              boundary_weight=float(p[geo['deg'] < geo['bulk']].sum()), boundary_fraction=float((geo['deg'] < geo['bulk']).mean()),
              S2=S2, S3=S3, local_D2=local_D2(S2), child_weights_depth1=[float(x) for x in p.reshape(8, 8 ** (L - 1)).sum(axis=1)],
              interface_weight={d: float(p[masks[d]].sum()) for d in masks}, interface_fraction={d: float(masks[d].mean()) for d in masks},
              interface_count={d: int(masks[d].sum()) for d in masks})
    return st

# ============================================================================================ solvers (own)
def rayleigh_ritz(H, Y):
    Q, _ = np.linalg.qr(Y); HQ = H @ Q; G = Q.conj().T @ HQ; G = 0.5 * (G + G.conj().T)
    th, U = np.linalg.eigh(G); X = Q @ U; HX = HQ @ U
    res = np.linalg.norm(HX - X * th[None, :], axis=0)
    return X, th, res

def cheb_fsi(H, K, m, lam_max, tol=1e-7, deg0=24, deg_max=120, max_passes=60, seed=1, X0=None, log=say, time_budget=1500.0):
    """Own Chebyshev-filtered subspace iteration for the lowest K eigenpairs: block m, Zhou-Saad scaled Chebyshev filter
    on [theta_m, lam_max] (theta_m = largest Ritz value of the block), Rayleigh-Ritz on the exact operator, stop when the
    lowest K residuals are < tol.  Returns Ritz values, vectors, residuals, number of block matvecs and the pass history."""
    N = H.shape[0]; rng = np.random.default_rng(seed); cplx = np.iscomplexobj(H.data)
    if X0 is None:
        X = rng.standard_normal((N, m)); X = X + 1j * rng.standard_normal((N, m)) if cplx else X
    else: X = X0.copy()
    t0 = time.time(); nmv = 0
    X, th, res = rayleigh_ritz(H, X); nmv += 1
    lam_lo = th[0]; deg = deg0; hist = []
    for p in range(max_passes):
        a = float(th[-1]); b = lam_max; e = (b - a) / 2.0; c = (b + a) / 2.0
        a0 = lam_lo - 0.05 * (a - lam_lo) - 1e-3
        sigma = e / (a0 - c); sigma1 = sigma
        Y = (H @ X - c * X) * (sigma1 / e); nmv += 1
        for i in range(2, deg + 1):
            sigma_new = 1.0 / (2.0 / sigma1 - sigma)
            Z = (H @ Y - c * Y) * (2.0 * sigma_new / e) - (sigma * sigma_new) * X; nmv += 1
            X, Y = Y, Z; sigma = sigma_new
        X, th, res = rayleigh_ritz(H, Y); nmv += 1; del Y
        lam_lo = min(lam_lo, float(th[0])); worst = float(res[:K].max())
        hist.append(dict(pass_=p, deg=deg, theta_1=float(th[0]), theta_K=float(th[K - 1]), theta_m=float(th[-1]), resK_max=worst,
                         resK_min=float(res[:K].min()), block_matvecs=nmv, seconds=time.time() - t0))
        log(f"      pass {p:2d} deg {deg:3d} nmv {nmv:5d}  theta_1={th[0]:.7f} theta_K={th[K-1]:.7f} theta_m={th[-1]:.7f}  res[:K] max {worst:.2e} min {res[:K].min():.2e}  {time.time()-t0:.0f}s rss {rss_gb():.2f}GB")
        if worst < tol: break
        if time.time() - t0 > time_budget: log('      time budget exhausted'); break
        deg = min(deg_max, int(deg * 1.5) if worst > 1e-2 else deg + 16)
    return th, X, res, nmv, hist

def solve_dense(H, K):
    w, V = sla.eigh(H.toarray()); X = V[:, :K]; th = w[:K]
    res = np.linalg.norm(H @ X - X * th[None, :], axis=0)
    return th, X, res, dict(method='dense scipy.linalg.eigh (full spectrum)', full_spectrum=w)

def solve_shift_invert(H, K, log=say):
    """ARPACK shift-invert: locate the bottom roughly with eigsh('SA'), then eigsh(sigma = est - 0.1, which='LM')."""
    t0 = time.time()
    w0 = spl.eigsh(H, k=1, which='SA', tol=1e-3, ncv=60, maxiter=20000, return_eigenvectors=False)
    sigma = float(w0[0]) - 0.1
    w, V = spl.eigsh(H, k=K, sigma=sigma, which='LM', tol=1e-12, ncv=max(2 * K + 4, 40), maxiter=10000)
    o = np.argsort(w); th = w[o]; X = V[:, o]; X = X / np.linalg.norm(X, axis=0)
    HX = H @ X; th = np.real(np.einsum('ij,ij->j', X.conj(), HX)); res = np.linalg.norm(HX - X * th[None, :], axis=0)
    return th, X, res, dict(method=f'ARPACK shift-invert (scipy eigsh, sigma={sigma:.4f}, splu, which=LM, tol 1e-12)', seconds=time.time() - t0, sigma=sigma)

def pair_average(th, V, res, K, spinor):
    """Tile densities of the lowest K states; Kramers (or accidental) near-degenerate pairs are averaged over the pair."""
    P = np.stack([tile_density(V[:, i], spinor) for i in range(K)])
    out = P.copy(); paired = [False] * K
    if spinor:
        i = 0
        while i + 1 < K:
            if abs(th[i + 1] - th[i]) < 1e-6 * max(1.0, abs(th[i])):
                avg = 0.5 * (P[i] + P[i + 1]); out[i] = avg; out[i + 1] = avg; paired[i] = paired[i + 1] = True; i += 2
            else: i += 1
    return out, paired

def solve(system, level, K=None):
    s = SYSTEMS[system]; spinor = s['links'] != 'trivial'
    if K is None: K = {3: 8, 4: 34, 5: 34}[level] if system in ('fr30', 'trivial') else (8 if level <= 4 else 8)
    if system in ('fr30_free', 'fr30_robin50'): K = min(K, 8)
    T0 = time.time(); say(f"=== solve {system} level {level} K={K}: {s['title']} ===")
    geo = geometry(system, level); H = build_H(system, geo); n = geo['n']
    herm = H - H.getH(); herm_dev = float(np.abs(herm.data).max()) if herm.nnz else 0.0; del herm
    say(f"   geometry n={n} dim={H.shape[0]} panels={len(geo['ea'])} nnz={H.nnz} frames={geo['nframes']} boundary tiles {(geo['deg']<geo['bulk']).sum()} links {geo['label_counts']} ({geo['build_s']:.1f}s) max|H-H^+|={herm_dev:.1e}")
    val = validate_against_objects(system, geo, H) if level <= 4 or (level == 5 and system == 'fr30') else None
    if val: say(f"   validation vs object builders: {val}")
    assert herm_dev == 0.0 and (val is None or (val['max_abs_dev'] == 0.0 and val['tile_order_identical']))
    masks = interface_masks(geo)
    lam_max = 2.0 * s['bulk']
    t0 = time.time()
    if level <= 3:
        th, X, res, info = solve_dense(H, K); info['seconds'] = time.time() - t0; cross = None
    elif level == 4:
        th, X, res, info = solve_shift_invert(H, K)
        m = K + (16 if K <= 8 else 16); tc = time.time()
        thc, Xc, resc, nmv, hist = cheb_fsi(H, K, m, lam_max, tol=1e-7, deg_max=100, log=say)
        pc_, _ = pair_average(thc, Xc, resc, K, spinor); pa, _ = pair_average(th, X, res, K, spinor)
        cross = dict(method=f'own Chebyshev FSI (block {m})', block_matvecs=int(nmv), seconds=time.time() - tc, max_eigenvalue_diff=float(np.abs(thc[:K] - th[:K]).max()),
                     max_residual=float(resc[:K].max()), ground_ipr_n_diff=float((IPR(pc_[0]) - IPR(pa[0])) * n), ground_density_L1_diff=float(np.abs(pc_[0] - pa[0]).sum()), history=hist)
        say(f"   cross-check shift-invert vs own ChebFSI: max|dlambda| {cross['max_eigenvalue_diff']:.1e}, dIPR*n {cross['ground_ipr_n_diff']:+.2e}, L1 density diff {cross['ground_density_L1_diff']:.1e}")
    else:
        m = K + 16; tol = 1e-5 if system == 'fr30_free' else 1e-7
        th, X, res, nmv, hist = cheb_fsi(H, K, m, lam_max, tol=tol, deg_max=120, log=say)
        info = dict(method=f'own Chebyshev-filtered subspace iteration (block {m}, deg <= 120, tol {tol:g})', block_matvecs=int(nmv), seconds=time.time() - t0, history=hist); cross = None
    th = th[:K]; X = X[:, :K]; res = res[:K]
    P, paired = pair_average(th, X, res, K, spinor)
    gaps = []
    for i in range(K):           # gap to the nearest eigenvalue outside the (near-)degenerate pair of state i
        others = [abs(th[j] - th[i]) for j in range(K) if j != i and abs(th[j] - th[i]) > 1e-6 * max(1.0, abs(th[i]))]
        gaps.append(min(others) if others else float('nan'))
    states = []
    for i in range(K):
        st = state_stats(P[i], geo, masks); st.update(index=i, eigenvalue=float(th[i]), residual=float(res[i]), gap=float(gaps[i]), paired=paired[i])
        states.append(st)
    g = states[0]
    say(f"   {info['method']} ({info['seconds']:.0f}s)")
    say(f"   lowest {min(K,8)}: {np.array2string(th[:8], precision=7, max_line_width=200)}  residuals: {np.array2string(res[:8], formatter={'float_kind': lambda x: f'{x:.1e}'}, max_line_width=200)}")
    say(f"   ground state: IPR*n={g['ipr_n']:.4f} P={1/g['ipr']:.1f} s50={g['s50']} s90={g['s90']} bw={g['boundary_weight']:.5f} interface w(1)={g['interface_weight'][1]:.4f} [frac {g['interface_fraction'][1]:.4f}] local D2(d)={np.round(g['local_D2'],3).tolist()}")
    if K >= 8: say(f"   lowest-8 mean IPR*n = {np.mean([s_['ipr_n'] for s_ in states[:8]]):.4f}")
    rec = dict(system=system, title=s['title'], level=level, n=n, dim=int(H.shape[0]), n_panels=int(len(geo['ea'])), nnz=int(H.nnz), K=K, spinor=spinor,
               label_counts=geo['label_counts'], hermiticity_dev=herm_dev, validation=val, solver=info, crosscheck_level4=cross,
               eigenvalues=th.tolist(), residuals=res.tolist(), states=states, interface_count={d: int(masks[d].sum()) for d in masks},
               boundary_count=int((geo['deg'] < geo['bulk']).sum()), total_seconds=time.time() - T0, max_rss_gb=rss_gb(),
               decoration={str(k): list(v) for k, v in decoration(system).items()})
    if 'full_spectrum' in info: rec['solver'] = {k: v for k, v in info.items() if k != 'full_spectrum'}; rec['full_spectrum_lowest64'] = info['full_spectrum'][:64].tolist()
    if 'history' in info: rec['solver']['history'] = info['history']
    jdump(rec, f'{TAG}_solve_{system}_L{level}.json')
    np.savez_compressed(os.path.join(RES, f'{TAG}_weights_{system}_L{level}.npz'), P=P.astype(np.float64), eigenvalues=th, residuals=res)
    say(f"   saved; total {rec['total_seconds']:.0f}s, max rss {rss_gb():.2f} GB")
    return rec

# ============================================================================================ D1: cost
def cost():
    out = dict(levels={}, python=sys.version.split()[0], numpy=np.__version__, omp=os.environ.get('OMP_NUM_THREADS'))
    rng = np.random.default_rng(0)
    for level in (5, 6):
        say(f"=== cost: FR30 pinned level {level} ===")
        r0 = rss_gb(); t0 = time.time(); geo = geometry('fr30', level); tg = time.time() - t0; r1 = rss_gb()
        t0 = time.time(); H = build_H('fr30', geo); tb = time.time() - t0; r2 = rss_gb()
        N = H.shape[0]; hbytes = H.data.nbytes + H.indices.nbytes + H.indptr.nbytes
        del geo['G']
        rec = dict(n=geo['n'], dim=N, nnz=int(H.nnz), nnz_per_tile=H.nnz / geo['n'], H_bytes=int(hbytes), H_GB=hbytes / 1e9, geometry_s=tg, build_s=tb,
                   rss_after_geometry_gb=r1, rss_after_build_gb=r2, matvec={})
        v = rng.standard_normal(N) + 1j * rng.standard_normal(N)
        for _ in range(2): H @ v
        reps = 10 if level == 5 else 5; t0 = time.time()
        for _ in range(reps): H @ v
        rec['matvec']['single'] = (time.time() - t0) / reps
        for m in (4, 8, 16, 32):
            Xb = rng.standard_normal((N, m)) + 1j * rng.standard_normal((N, m)); H @ Xb; t0 = time.time(); H @ Xb; t1 = time.time() - t0
            t0 = time.time(); Q, _ = np.linalg.qr(Xb); tq = time.time() - t0
            t0 = time.time(); G = Xb.conj().T @ Xb; tgm = time.time() - t0
            rec['matvec'][f'block{m}'] = dict(block_matvec_s=t1, per_vector_s=t1 / m, qr_s=tq, gram_s=tgm, block_bytes=int(Xb.nbytes))
            del Xb, Q
        # one LOBPCG (block 4) iteration cost: scipy lobpcg, diag preconditioner, difference between maxiter=6 and maxiter=2 from the same start
        X0 = rng.standard_normal((N, 4)) + 1j * rng.standard_normal((N, 4)); dinv = 1.0 / H.diagonal().real
        M = spl.LinearOperator(H.shape, matvec=lambda x: dinv * x, matmat=lambda B: dinv[:, None] * B, dtype=complex)
        import warnings
        with warnings.catch_warnings():
            warnings.simplefilter('ignore')
            t0 = time.time(); spl.lobpcg(H, X0.copy(), M=M, largest=False, tol=1e-12, maxiter=2); ta = time.time() - t0
            t0 = time.time(); spl.lobpcg(H, X0.copy(), M=M, largest=False, tol=1e-12, maxiter=8); tb_ = time.time() - t0
        rec['lobpcg_block4_s_per_iteration'] = (tb_ - ta) / 6.0
        rec['max_rss_gb'] = rss_gb()
        say(f"   n={geo['n']} dim={N} nnz={H.nnz} ({H.nnz/geo['n']:.3f}/tile) H={hbytes/1e9:.3f} GB; geometry {tg:.1f}s build {tb:.1f}s; rss after build {r2:.2f} GB (max {rss_gb():.2f})")
        say(f"   matvec single {rec['matvec']['single']*1e3:.1f} ms; block: " + '; '.join(f"m={m}: {rec['matvec'][f'block{m}']['block_matvec_s']:.3f}s ({rec['matvec'][f'block{m}']['per_vector_s']*1e3:.1f} ms/vec, qr {rec['matvec'][f'block{m}']['qr_s']:.2f}s)" for m in (4, 8, 16, 32)))
        say(f"   scipy lobpcg block 4: {rec['lobpcg_block4_s_per_iteration']:.3f} s/iteration")
        out['levels'][level] = rec; del H, v, X0
    jdump(out, f'{TAG}_cost.json'); return out

# ============================================================================================ exact Dirichlet box
def dirichlet_box(L):
    """6 - A on the Z^3 box {1..M}^3, M = 2^L, Dirichlet walls: ground state psi = prod sin(pi x_i/(M+1)); exact sums."""
    M = 2 ** L; x = np.arange(1, M + 1); s = np.sin(np.pi * x / (M + 1)) ** 2; w = s / s.sum()     # 1-d weights, sum 1
    ipr1 = float((w ** 2).sum()); n = M ** 3; ipr = ipr1 ** 3
    S2 = []
    for d in range(L + 1):
        W = w.reshape(2 ** d, M // 2 ** d).sum(axis=1); S2.append(float((W ** 2).sum() ** 3))
    lam1 = 6 - 6 * np.cos(np.pi / (M + 1)); lam2 = 6 - 4 * np.cos(np.pi / (M + 1)) - 2 * np.cos(2 * np.pi / (M + 1))
    return dict(level=L, M=M, n=n, ipr=ipr, ipr_n=ipr * n, ipr_n_closed_form=3.375 * (M / (M + 1)) ** 3, S2=S2, local_D2=local_D2(S2), lambda_1=float(lam1), gap=float(lam2 - lam1))

# ============================================================================================ analysis (D2 + D3)
def D2_window(ipr1, n1, ipr2, n2): return float(3.0 * np.log(ipr1 / ipr2) / np.log(n2 / n1))
def load_solve(system, level): return jload(f'{TAG}_solve_{system}_L{level}.json')
def load_weights(system, level):
    p = os.path.join(RES, f'{TAG}_weights_{system}_L{level}.npz'); return np.load(p) if os.path.exists(p) else None

def stored_level6():
    """Stored level-6 artifacts (phase5a): ground-state weights, lowest-8 records; marked as stored in the output."""
    out = {}
    p = os.path.join(RES, 'phase5a_fr30_level6_groundstate_weights.npy')
    if os.path.exists(p):
        w = np.load(p); out['fr30'] = dict(level=6, n=len(w), ipr=IPR(w), ipr_n=IPR(w) * len(w), ipr3=float((w ** 3).sum()), S2=S2_profile(w, 6), source='phase5a_fr30_level6_groundstate_weights.npy (LOBPCG block 4, res 3.5e-7, gap 1.08e-4)',
                          residual=3.49e-7, gap=1.082e-4)
        out['fr30']['local_D2'] = local_D2(out['fr30']['S2'])
    es = jload('phase5a_edge_states_level6.json')
    if es:
        ep = es['pinned']['eigenpairs']
        out['fr30_lowest8'] = dict(level=6, n=262144, eigenvalues=[e['eigenvalue'] for e in ep[:8]], residuals=[e['residual'] for e in ep[:8]], ipr=[e['ipr'] for e in ep[:8]],
                                   ipr_n=[e['ipr_n'] for e in ep[:8]], interface_weight=[e['interface_weight'] for e in ep[:8]], boundary_weight=[e['boundary_weight'] for e in ep[:8]],
                                   source='phase5a_edge_states_level6.json (ChebFSI block 24, res <= 9e-7)')
    cu = jload('phase5a_scaling_controls_cube.json')
    if cu:
        r6 = [r for r in cu['records'] if r['level'] == 6]
        if r6:
            r = r6[0]; out['cube'] = dict(level=6, n=r['n'], ipr=r['ipr'], ipr_n=r['ipr_n'], S2=[r['S2'][str(d)] for d in range(7)], residual=max(r['residuals'][:2]), gap=r['eigenvalues'][2] - r['eigenvalues'][0],
                                        interface_weight={int(k): v for k, v in r['interface_weight'].items()}, boundary_weight=r['boundary_weight'], source='phase5a_scaling_controls_cube.json (LOBPCG block 6, tol 1e-7)')
            out['cube']['local_D2'] = local_D2(out['cube']['S2'])
    sc = jload('phase5a_scaling.json')
    out['scaling_json_present'] = sc is not None
    return out

def analyze():
    lines = []
    def L(s=''): lines.append(s); print(s, flush=True)
    out = dict(generated=time.strftime('%Y-%m-%d %H:%M:%S'), cost=jload(f'{TAG}_cost.json'))
    L("PHASE V-B / WORKSTREAM D (light): LEVEL-7 COST, D_2 SCALING WINDOWS, ENERGY-RESOLVED LEVEL 5, FOUR EXPLANATIONS")
    L("All numbers are computed in this session by audit/phase5b_d_scaling.py unless marked [stored: file].  Residuals ||H psi - lambda psi||_2.")
    L("Uncertainty model: eigenvector angle theta <= res/gap (gap = distance to the nearest eigenvalue outside the Kramers pair); |dIPR|/IPR ~ 2 theta;")
    L("  dD_2(window) = 3 sqrt((dIPR_1/IPR_1)^2 + (dIPR_2/IPR_2)^2) / ln(n_2/n_1).  Kramers partners are averaged (their densities coincide up to solver error).")
    recs = {}
    for system in SYSTEMS:
        for level in (3, 4, 5):
            r = load_solve(system, level)
            if r: recs[(system, level)] = r
    st6 = stored_level6(); out['stored_level6'] = st6
    # ---------------------------------------------------------------- 1. recomputation table
    L("\n1. INDEPENDENT RECOMPUTATION (own builder + own solvers) versus stored claims")
    claims = {('fr30', 3): 6.424, ('fr30', 4): 9.146, ('fr30', 5): 19.930, ('cube', 3): 7.836, ('cube', 4): 10.292, ('cube', 5): 17.209,
              ('trivial', 3): 2.259, ('trivial', 4): 2.885, ('trivial', 5): 3.264, ('randdec108', 4): 7.990, ('randdec108', 5): 35.829}
    claimsE = {('fr30', 3): 9.378470, ('fr30', 4): 8.919634, ('fr30', 5): 8.797011, ('cube', 3): 1.913948, ('cube', 4): 1.861013, ('cube', 5): 1.852106,
               ('trivial', 3): 1.669512, ('trivial', 4): 0.502729, ('trivial', 5): 0.138602}
    L(f"   {'system':<13}{'L':>2}{'n':>7}{'dim':>7} {'lambda_1':>10} {'res_1':>8} {'gap':>9} {'IPR*n':>8} {'claim':>7} {'dIPR*n':>8} {'low8 IPR*n':>10} {'bw':>8} {'w(1)':>7} {'frac1':>6} {'solver':<40} {'s':>6} {'GB':>5}")
    table1 = []
    for (system, level), r in sorted(recs.items(), key=lambda kv: (list(SYSTEMS).index(kv[0][0]), kv[0][1])):
        g = r['states'][0]; low8 = float(np.mean([s['ipr_n'] for s in r['states'][:8]])) if r['K'] >= 8 else float('nan')
        c = claims.get((system, level)); cE = claimsE.get((system, level))
        row = dict(system=system, level=level, n=r['n'], dim=r['dim'], lambda_1=r['eigenvalues'][0], res_1=r['residuals'][0], gap=g['gap'], ipr_n=g['ipr_n'], claim=c,
                   dipr_n=(g['ipr_n'] - c) if c else None, claimE=cE, dE=(r['eigenvalues'][0] - cE) if cE else None, low8_ipr_n=low8, bw=g['boundary_weight'], w1=g['interface_weight']['1'],
                   frac1=g['interface_fraction']['1'], solver=r['solver']['method'], seconds=r['total_seconds'], rss=r['max_rss_gb'], validation=r['validation'], crosscheck=r.get('crosscheck_level4'))
        table1.append(row)
        cstr = f'{c:.3f}' if c else '-'; dstr = f"{g['ipr_n'] - c:+.4f}" if c else '-'
        L(f"   {system:<13}{level:>2}{r['n']:>7}{r['dim']:>7} {r['eigenvalues'][0]:>10.6f} {r['residuals'][0]:>8.1e} {g['gap']:>9.2e} {g['ipr_n']:>8.3f} {cstr:>7} {dstr:>8} {low8:>10.3f} {g['boundary_weight']:>8.5f} {g['interface_weight']['1']:>7.4f} {g['interface_fraction']['1']:>6.3f} {r['solver']['method'][:40]:<40} {r['total_seconds']:>6.0f} {r['max_rss_gb']:>5.2f}")
        if r['validation']: L(f"      validation vs object builders: max|dH| = {r['validation']['max_abs_dev']:.1e}, tile order identical {r['validation']['tile_order_identical']}, degrees identical {r['validation']['degrees_identical']}, panels {r['validation']['n_edges']} = {r['validation']['n_edges_ref']}")
        if r.get('crosscheck_level4'): cc = r['crosscheck_level4']; L(f"      level-4 cross-check shift-invert vs own ChebFSI: max|dlambda| {cc['max_eigenvalue_diff']:.1e}, dIPR*n {cc['ground_ipr_n_diff']:+.1e}, L1 density diff {cc['ground_density_L1_diff']:.1e} ({cc['block_matvecs']} block matvecs)")
        if cE: L(f"      bottom vs stored {cE:.6f}: {r['eigenvalues'][0]-cE:+.1e}")
    out['recomputation'] = table1
    # stored weight-file verification
    L("\n   verification of stored tile-density weight files (IPR*n recomputed from the .npy; L1 distance to this session's ground-state density):")
    wf = []
    for system, fn in [('fr30', 'phase5a_fr30_level{L}_groundstate_weights.npy'), ('cube', 'phase5a_cube_level{L}_groundstate_weights.npy')]:
        for level in (3, 4, 5, 6):
            p = os.path.join(RES, fn.format(L=level))
            if not os.path.exists(p): continue
            w = np.load(p); row = dict(system=system, level=level, file=os.path.basename(p), n=len(w), ipr_n=IPR(w) * len(w), sum=float(w.sum()))
            wz = load_weights(system, level)
            if wz is not None: row['L1_to_this_session'] = float(np.abs(wz['P'][0] - w).sum()); row['ipr_n_diff'] = float(IPR(wz['P'][0]) - IPR(w)) * len(w)
            wf.append(row); L(f"      {row['file']:<48} n={len(w):>7} sum={w.sum():.6f} IPR*n={row['ipr_n']:.4f}" + (f"  L1 to own density {row['L1_to_this_session']:.2e}, dIPR*n {row['ipr_n_diff']:+.2e}" if 'L1_to_this_session' in row else '  (no own level-6 state: stored only)'))
    out['weight_files'] = wf
    # ---------------------------------------------------------------- 2. D2 windows
    L("\n2. D_2 ESTIMATES.  IPR_q ~ n^{-(q-1) D_q/3}: window estimate D_2(L1->L2) = 3 ln(IPR_1/IPR_2)/ln(n_2/n_1); D_3 likewise with (q-1)=2.")
    def series(system):
        s = {}
        for level in (3, 4, 5):
            r = recs.get((system, level))
            if r:
                g = r['states'][0]; theta = g['residual'] / g['gap'] if g['gap'] > 0 else 0.0
                s[level] = dict(n=r['n'], ipr=g['ipr'], ipr3=g['ipr3'], rel=2 * theta, S2=g['S2'], local_D2=g['local_D2'],
                                low8=[st['ipr'] for st in r['states'][:8]] if r['K'] >= 8 else None,
                                low8_rel=[2 * st['residual'] / st['gap'] if st['gap'] > 0 else 0.0 for st in r['states'][:8]] if r['K'] >= 8 else None, source='this session')
        if system == 'fr30' and 'fr30' in st6:
            z = st6['fr30']; s[6] = dict(n=z['n'], ipr=z['ipr'], ipr3=z['ipr3'], rel=2 * z['residual'] / z['gap'], S2=z['S2'], local_D2=z['local_D2'], source='stored: ' + z['source'],
                                        low8=st6['fr30_lowest8']['ipr'] if 'fr30_lowest8' in st6 else None,
                                        low8_rel=[2 * r_ / 1.0e-4 for r_ in st6['fr30_lowest8']['residuals']] if 'fr30_lowest8' in st6 else None)
        if system == 'cube' and 'cube' in st6:
            z = st6['cube']; s[6] = dict(n=z['n'], ipr=z['ipr'], ipr3=None, rel=2 * z['residual'] / z['gap'], S2=z['S2'], local_D2=z['local_D2'], source='stored: ' + z['source'], low8=None, low8_rel=None)
        return s
    windows = [(3, 4), (4, 5), (5, 6), (3, 5), (4, 6), (3, 6)]
    d2 = {}
    for system in ('fr30', 'cube', 'trivial', 'randdec108'):
        s = series(system)
        if not s: continue
        d2[system] = dict(levels={lv: dict(n=v['n'], ipr_n=v['ipr'] * v['n'], rel_ipr_err=v['rel'], source=v['source']) for lv, v in s.items()}, windows={})
        L(f"\n   {SYSTEMS[system]['title']}")
        L(f"   {'window':>7} {'D2 ground':>10} {'+-':>7} {'D2 low8':>8} {'+-':>7} {'D3 ground':>10} | {'alpha':>6}   sources")
        for (a, b) in windows:
            if a in s and b in s:
                va, vb = s[a], s[b]; D2 = D2_window(va['ipr'], va['n'], vb['ipr'], vb['n']); err = 3 * np.hypot(va['rel'], vb['rel']) / np.log(vb['n'] / va['n'])
                D3 = (3.0 / 2.0) * np.log(va['ipr3'] / vb['ipr3']) / np.log(vb['n'] / va['n']) if (va['ipr3'] and vb['ipr3']) else float('nan')
                if va['low8'] and vb['low8']:
                    D2l = D2_window(np.mean(va['low8']), va['n'], np.mean(vb['low8']), vb['n'])
                    errl = 3 * np.hypot(np.mean(va['low8_rel']) / np.sqrt(4), np.mean(vb['low8_rel']) / np.sqrt(4)) / np.log(vb['n'] / va['n'])
                else: D2l = errl = float('nan')
                row = dict(window=f'{a}->{b}', D2_ground=D2, D2_ground_err=err, D2_low8=D2l, D2_low8_err=errl, D3_ground=D3, alpha=D2 / 3, sources=[va['source'][:6], vb['source'][:6]])
                d2[system]['windows'][f'{a}->{b}'] = row
                L(f"   {a}->{b:<4} {D2:>10.3f} {err:>7.3f} {D2l:>8.3f} {errl:>7.3f} {D3:>10.3f} | {D2/3:>6.3f}   {va['source'][:6]}/{vb['source'][:6]}")
        L("   box counting inside each level: local D2(d) = log2(S2(d-1)/S2(d)), d = 1..L (3 = uniform fill, 2 = surface-like):")
        for lv, v in s.items(): L(f"      L{lv}: {np.round(v['local_D2'], 3).tolist()}   mean over d>=2: {np.mean(v['local_D2'][1:]):.3f}   [{v['source'][:6]}]")
        d2[system]['local_D2'] = {lv: v['local_D2'] for lv, v in s.items()}
        # least-squares over all available levels
        lv = sorted(s); x = np.log([s[l]['n'] for l in lv]); y = np.log([s[l]['ipr'] for l in lv])
        if len(lv) >= 3:
            slope, inter = np.polyfit(x, y, 1); resid = y - (slope * x + inter); se = np.sqrt(resid @ resid / max(len(lv) - 2, 1) / ((x - x.mean()) ** 2).sum())
            d2[system]['lsq_all'] = dict(levels=lv, D2=-3 * slope, D2_err=3 * se, alpha=-slope)
            L(f"   least squares over levels {lv}: D2 = {-3*slope:.3f} +- {3*se:.3f} (alpha = {-slope:.3f}; the +- is the scatter around a single power law, not a solver error)")
    out['D2'] = d2
    # exact Dirichlet box
    L("\n   exact Dirichlet box 6 - A on {1..M}^3 (M = 2^L): IPR*n = 3.375 (M/(M+1))^3 exactly; this is the trivial-link control on the CUBE geometry (unit-cube tiles, trivial links)")
    box = {L_: dirichlet_box(L_) for L_ in range(3, 8)}; out['dirichlet_box'] = box
    for L_, b in box.items(): L(f"      L{L_}: M={b['M']:>3} n={b['n']:>8} IPR*n = {b['ipr_n']:.4f} (closed form {b['ipr_n_closed_form']:.4f})  lambda_1 = {b['lambda_1']:.6f} gap {b['gap']:.2e}  local D2(d) = {np.round(b['local_D2'], 3).tolist()}")
    for (a, b_) in windows:
        if b_ <= 7: L(f"      box window {a}->{b_}: D2 = {D2_window(box[a]['ipr'], box[a]['n'], box[b_]['ipr'], box[b_]['n']):.3f}")
    tr = d2.get('trivial')
    if tr: L(f"      trivial-link CHAIR control IPR*n (this session): " + ', '.join(f"L{lv}: {v['ipr_n']:.3f}" for lv, v in tr['levels'].items()) + "  [stored L6: 3.471]; the chair domain is a cube minus an octant, not a box, so its constant differs from 3.375 (finite-size approach to a constant is the point)")
    # ---------------------------------------------------------------- 3. energy-resolved level 5
    L("\n3. ENERGY-RESOLVED ANALYSIS AT LEVEL 5 (FR30 pinned, lowest K states; Kramers pairs averaged): IPR*n, interface weights w(1), w(2), boundary weight vs energy")
    r5 = recs.get(('fr30', 5)); er = None
    if r5:
        sts = r5['states']; lam = np.array([s['eigenvalue'] for s in sts]); x = lam - lam[0]
        L(f"   {'#':>3} {'lambda':>10} {'lambda-lambda_1':>15} {'res':>8} {'IPR*n':>8} {'s50':>5} {'w(1)':>7} {'w(2)':>7} {'w(3)':>7} {'bw':>8} {'D2(1)':>6} {'D2(L)':>6}")
        for s in sts:
            L(f"   {s['index']:>3} {s['eigenvalue']:>10.6f} {s['eigenvalue']-lam[0]:>15.6f} {s['residual']:>8.1e} {s['ipr_n']:>8.3f} {s['s50']:>5} {s['interface_weight']['1']:>7.4f} {s['interface_weight']['2']:>7.4f} {s['interface_weight']['3']:>7.4f} {s['boundary_weight']:>8.5f} {s['local_D2'][0]:>6.3f} {s['local_D2'][-1]:>6.3f}")
        ipr_n = np.array([s['ipr_n'] for s in sts]); w1 = np.array([s['interface_weight']['1'] for s in sts]); bw = np.array([s['boundary_weight'] for s in sts])
        dist = sorted(set(np.round(lam, 9))); spac = np.diff(dist)
        # Spearman rank correlations with energy over distinct pairs
        from scipy.stats import spearmanr
        idx = [i for i in range(len(sts)) if i % 2 == 0]
        rho1 = spearmanr(lam[idx], ipr_n[idx]); rho2 = spearmanr(lam[idx], w1[idx])
        er = dict(K=len(sts), span=float(lam[-1] - lam[0]), n_distinct=len(dist), spacings=spac.tolist(), max_spacing=float(spac.max()), median_spacing=float(np.median(spac)),
                  ipr_n_min=float(ipr_n.min()), ipr_n_max=float(ipr_n.max()), ipr_n_mean=float(ipr_n.mean()), w1_min=float(w1.min()), w1_max=float(w1.max()), w1_mean=float(w1.mean()),
                  bw_max=float(bw.max()), interface1_fraction=sts[0]['interface_fraction']['1'], spearman_E_iprn=[float(rho1.statistic), float(rho1.pvalue)], spearman_E_w1=[float(rho2.statistic), float(rho2.pvalue)])
        L(f"   {len(sts)} states span {er['span']:.5f}; {len(dist)} distinct levels, spacings median {er['median_spacing']:.2e} max {er['max_spacing']:.2e} (largest spacing / median = {er['max_spacing']/er['median_spacing']:.1f}): a separate band would show a spacing >> median")
        L(f"   IPR*n in [{ipr_n.min():.2f}, {ipr_n.max():.2f}] (mean {ipr_n.mean():.2f}); w(1) in [{w1.min():.4f}, {w1.max():.4f}] (mean {w1.mean():.4f}; tile fraction {er['interface1_fraction']:.4f}, i.e. enrichment {w1.mean()/er['interface1_fraction']:.2f}); boundary weight <= {bw.max():.5f}")
        L(f"   Spearman(E, IPR*n) = {rho1.statistic:+.3f} (p={rho1.pvalue:.2g}); Spearman(E, w(1)) = {rho2.statistic:+.3f} (p={rho2.pvalue:.2g}) over the {len(idx)} distinct pairs")
        t5 = recs.get(('trivial', 5))
        if t5:
            tw = np.array([s['interface_weight']['1'] for s in t5['states']]); ti = np.array([s['ipr_n'] for s in t5['states']])
            L(f"   trivial-link control, same K at level 5: IPR*n in [{ti.min():.2f}, {ti.max():.2f}], w(1) in [{tw.min():.4f}, {tw.max():.4f}] (enrichment {tw.mean()/er['interface1_fraction']:.2f})")
            er['trivial_w1_range'] = [float(tw.min()), float(tw.max())]; er['trivial_iprn_range'] = [float(ti.min()), float(ti.max())]
    out['energy_resolved_L5'] = er
    # ---------------------------------------------------------------- 4. explanation tests (D3)
    L("\n4. TESTS OF THE FOUR EXPLANATIONS")
    ex = {}
    # (3) interface network tests, computed from own densities at levels 3-5 and the stored level-6 density
    L("\n   (3) interface-network tests: P = 1/IPR vs |I_1| = T_L; weight on I_1 vs fraction; overlap with the uniform state on I_d; IPR of the restriction to I_1 / complement; weight profile vs tile distance from I_1")
    L(f"   {'L':>2} {'n':>7} {'T_L':>6} {'P':>8} {'P/T_L':>6} {'w(1)':>6} {'f(1)':>6} {'P_I/T_L':>7} {'P_notI/|~I|':>11} {'ovl u(I1)':>9} {'ovl u(I2)':>9} {'ovl u(I3)':>9} | weight at tile distance 0,1,2,3,>=4 from I_1 (fractions of tiles in brackets)")
    net = {}
    for level in (3, 4, 5, 6):
        if level <= 5:
            r = recs.get(('fr30', level)); wz = load_weights('fr30', level)
            if not (r and wz is not None): continue
            p = wz['P'][0]; src = 'own'
        else:
            pth = os.path.join(RES, 'phase5a_fr30_level6_groundstate_weights.npy')
            if not os.path.exists(pth): continue
            p = np.load(pth); src = 'stored'
        geo = geometry('fr30', level); masks = interface_masks(geo); n = geo['n']
        I1 = masks[1]; P = 1 / IPR(p); pI = p[I1]; pN = p[~I1]
        PI = (pI.sum() ** 2) / (pI ** 2).sum(); PN = (pN.sum() ** 2) / (pN ** 2).sum() if pN.sum() > 0 else float('nan')
        ovl = {d: float(np.minimum(p, masks[d] / masks[d].sum()).sum()) for d in (1, 2, 3) if d in masks}
        adj = tile_adjacency(geo); dist = graph_distance(adj, I1)
        prof = [float(p[dist == k].sum()) for k in range(4)] + [float(p[dist >= 4].sum())]
        frac = [float((dist == k).mean()) for k in range(4)] + [float((dist >= 4).mean())]
        row = dict(level=level, n=n, T_L=int(I1.sum()), P=P, P_over_TL=P / I1.sum(), w1=float(pI.sum()), f1=float(I1.mean()), P_I_over_TL=PI / I1.sum(), P_notI_over_count=PN / (~I1).sum(),
                   overlap_uniform_on_Id=ovl, weight_vs_distance=prof, tile_fraction_vs_distance=frac, source=src)
        net[level] = row
        L(f"   {level:>2} {n:>7} {int(I1.sum()):>6} {P:>8.1f} {P/I1.sum():>6.3f} {pI.sum():>6.3f} {I1.mean():>6.3f} {PI/I1.sum():>7.3f} {PN/(~I1).sum():>11.4f} {ovl.get(1,float('nan')):>9.3f} {ovl.get(2,float('nan')):>9.3f} {ovl.get(3,float('nan')):>9.3f} | " + ' '.join(f"{w:.3f}[{f:.3f}]" for w, f in zip(prof, frac)) + f"  ({src})")
    ex['interface_network'] = net
    # (4) boundary tests: free / Robin / pinned, and restriction to the central child
    L("\n   (4) boundary-condition tests: pinned vs Robin(t=0.5) vs free at levels 3-5; restriction of the pinned level-L state to its central level-(L-1) child (tiles 0..n/8-1) vs the pinned level-(L-1) state")
    L(f"   {'L':>2} {'diag':<8} {'lambda_1':>10} {'IPR*n':>8} {'bw':>8} {'bfrac':>6} {'w(1)':>7}")
    bnd = {}
    for level in (3, 4, 5):
        for system, name in [('fr30', 'pinned'), ('fr30_robin50', 'robin.5'), ('fr30_free', 'free')]:
            r = recs.get((system, level))
            if r:
                g = r['states'][0]; bnd[f'{name}_L{level}'] = dict(level=level, lambda_1=r['eigenvalues'][0], ipr_n=g['ipr_n'], bw=g['boundary_weight'], bfrac=g['boundary_fraction'], w1=g['interface_weight']['1'], residual=r['residuals'][0])
                L(f"   {level:>2} {name:<8} {r['eigenvalues'][0]:>10.6f} {g['ipr_n']:>8.3f} {g['boundary_weight']:>8.5f} {g['boundary_fraction']:>6.3f} {g['interface_weight']['1']:>7.4f}")
    L("   restriction to the central child (renormalised; IPR*(n/8) of the restriction, compared with the pinned ground state one level lower):")
    restr = {}
    for level in (4, 5, 6):
        if level <= 5:
            wz = load_weights('fr30', level); p = wz['P'][0] if wz is not None else None; src = 'own'
        else:
            pth = os.path.join(RES, 'phase5a_fr30_level6_groundstate_weights.npy'); p = np.load(pth) if os.path.exists(pth) else None; src = 'stored'
        if p is None: continue
        n = len(p); m = n // 8; cw = p.reshape(8, m).sum(axis=1)
        rows = []
        for ch in range(8):
            q = p[ch * m:(ch + 1) * m]; q = q / q.sum(); rows.append(dict(child=ch, weight=float(cw[ch]), ipr_n_restricted=IPR(q) * m, local_D2=local_D2(S2_profile(q, level - 1))))
        prev = recs.get(('fr30', level - 1)); prev_ipr_n = prev['states'][0]['ipr_n'] if prev else float('nan')
        prev_p = load_weights('fr30', level - 1)['P'][0] if load_weights('fr30', level - 1) is not None else None
        ovl0 = float(np.minimum(p[:m] / p[:m].sum(), prev_p).sum()) if prev_p is not None else float('nan')
        restr[level] = dict(child_rows=rows, pinned_prev_level_ipr_n=prev_ipr_n, overlap_central_restriction_with_prev_level_state=ovl0, source=src)
        L(f"   L{level} ({src}): central child weight {cw[0]:.4f}, IPR*(n/8) of restriction {rows[0]['ipr_n_restricted']:.3f} vs pinned L{level-1} IPR*n {prev_ipr_n:.3f}; overlap sum min(p_restr, p_L-1) = {ovl0:.3f}; "
          f"other children IPR*(n/8): {[round(r_['ipr_n_restricted'], 2) for r_ in rows[1:]]} (weights {[round(r_['weight'], 3) for r_ in rows[1:]]})")
    ex['boundary'] = dict(table=bnd, restriction=restr)
    # (1)/(2): summary statistics from the D2 table
    fr = d2.get('fr30', {}); w_ = fr.get('windows', {})
    ex['D2_summary'] = {k: (v['D2_ground'], v['D2_ground_err']) for k, v in w_.items()}
    L("\n   (1)/(2) scale dependence of the exponents (FR30): window D2(ground): " + ', '.join(f"{k}: {v['D2_ground']:.2f}+-{v['D2_ground_err']:.2f}" for k, v in w_.items()))
    L("      window D2(lowest 8): " + ', '.join(f"{k}: {v['D2_low8']:.2f}" for k, v in w_.items()) + ";  D3(ground): " + ', '.join(f"{k}: {v['D3_ground']:.2f}" for k, v in w_.items()))
    cu = d2.get('cube', {}).get('windows', {}); trv = d2.get('trivial', {}).get('windows', {}); rd = d2.get('randdec108', {}).get('windows', {})
    L("      cube control D2(ground): " + ', '.join(f"{k}: {v['D2_ground']:.2f}" for k, v in cu.items()))
    L("      trivial control D2(ground): " + ', '.join(f"{k}: {v['D2_ground']:.2f}" for k, v in trv.items()) + "   (exact Dirichlet box: " + ', '.join(f"{a}->{b}: {D2_window(box[a]['ipr'], box[a]['n'], box[b]['ipr'], box[b]['n']):.2f}" for a, b in windows if b <= 7) + ")")
    L("      randdec108 D2(ground): " + ', '.join(f"{k}: {v['D2_ground']:.2f}" for k, v in rd.items()))
    out['explanations'] = ex
    # ---------------------------------------------------------------- 5. level-7 cost
    c = out['cost']
    if c:
        L("\n5. LEVEL-7 COST ESTIMATE (measured at levels 5 and 6 in this session, OMP_NUM_THREADS=1, shared machine)")
        l5, l6 = c['levels']['5'], c['levels']['6']
        L(f"   {'level':>5} {'n':>8} {'dim':>8} {'nnz':>10} {'nnz/tile':>8} {'H GB':>6} {'build s':>7} {'matvec ms':>9} {'m=4 s':>7} {'m=8 s':>7} {'m=16 s':>7} {'m=32 s':>7} {'qr32 s':>7} {'lobpcg4 s/it':>12} {'rss GB':>6}")
        for lv, r in (('5', l5), ('6', l6)):
            L(f"   {lv:>5} {r['n']:>8} {r['dim']:>8} {r['nnz']:>10} {r['nnz_per_tile']:>8.3f} {r['H_GB']:>6.3f} {r['geometry_s']+r['build_s']:>7.1f} {r['matvec']['single']*1e3:>9.1f} {r['matvec']['block4']['block_matvec_s']:>7.3f} {r['matvec']['block8']['block_matvec_s']:>7.3f} {r['matvec']['block16']['block_matvec_s']:>7.3f} {r['matvec']['block32']['block_matvec_s']:>7.3f} {r['matvec']['block32']['qr_s']:>7.2f} {r['lobpcg_block4_s_per_iteration']:>12.3f} {r['max_rss_gb']:>6.2f}")
        f_mv = l6['matvec']['single'] / l5['matvec']['single']; f_b4 = l6['matvec']['block4']['block_matvec_s'] / l5['matvec']['block4']['block_matvec_s']; f_lo = l6['lobpcg_block4_s_per_iteration'] / l5['lobpcg_block4_s_per_iteration']
        nnz7 = 8 * l6['nnz'] + (l6['nnz'] - 8 * l5['nnz']) * 0.5     # nnz/tile converges geometrically (boundary fraction halves per level)
        n7 = 8 * l6['n']; dim7 = 2 * n7; HGB7 = (nnz7 * 20 + (dim7 + 1) * 4) / 1e9; vec7 = dim7 * 16 / 1e9
        est = dict(n=n7, dim=dim7, nnz=nnz7, nnz_per_tile=nnz7 / n7, H_GB_complex128_int32=HGB7, H_GB_complex64=(nnz7 * 12 + (dim7 + 1) * 4) / 1e9, vector_GB=vec7,
                   scale_matvec_6_over_5=f_mv, scale_block4_6_over_5=f_b4, scale_lobpcg_6_over_5=f_lo,
                   matvec_single_s=l6['matvec']['single'] * f_mv, block4_s=l6['matvec']['block4']['block_matvec_s'] * f_b4, block8_s=l6['matvec']['block8']['block_matvec_s'] * f_b4,
                   block16_s=l6['matvec']['block16']['block_matvec_s'] * f_b4, block24_s=0.5 * (l6['matvec']['block16']['block_matvec_s'] + l6['matvec']['block32']['block_matvec_s']) * f_b4,
                   block32_s=l6['matvec']['block32']['block_matvec_s'] * f_b4, lobpcg_block4_s_per_it=l6['lobpcg_block4_s_per_iteration'] * f_lo)
        L(f"   scale factors 6/5 measured: single matvec x{f_mv:.2f}, block-4 matvec x{f_b4:.2f}, lobpcg iteration x{f_lo:.2f} (ideal 8); the same factors are applied 6 -> 7")
        L(f"   level 7: n = {n7}, dim = {dim7}, nnz ~ {nnz7/1e6:.1f} M ({nnz7/n7:.2f}/tile), H = {HGB7:.2f} GB (complex128 + int32 indices; {est['H_GB_complex64']:.2f} GB in complex64), one vector = {vec7*1e3:.0f} MB")
        L(f"   level 7 per-operation: single matvec {est['matvec_single_s']:.2f} s; block matvec m=4 {est['block4_s']:.2f} s, m=8 {est['block8_s']:.2f} s, m=16 {est['block16_s']:.2f} s, m=24 ~{est['block24_s']:.2f} s, m=32 {est['block32_s']:.2f} s; scipy LOBPCG block-4 iteration {est['lobpcg_block4_s_per_it']:.2f} s")
        # iteration counts from the stored level-5/6 histories and the gap extrapolation
        gaps = {4: 2.92e-2, 5: 1.969e-3, 6: 1.082e-4}; ratio = (gaps[6] / gaps[5]) / (gaps[5] / gaps[4])   # second ratio of gap ratios
        g7 = gaps[6] * (gaps[6] / gaps[5]) * ratio ** 0.5
        it_lob = {5: 972, 6: 3100}; p_lob = np.log(it_lob[6] / it_lob[5]) / np.log(gaps[5] / gaps[6])
        it7_lob = it_lob[6] * (gaps[6] / g7) ** p_lob; it7_lob_hi = it_lob[6] * (gaps[6] / g7) ** 0.5
        cheb = dict(L5_K128_block192=488, L6_K8_block24=1373, L6_K4_block32_stalled=488)
        nmv7_lo = cheb['L6_K8_block24'] * (gaps[6] / g7) ** p_lob; nmv7_hi = cheb['L6_K8_block24'] * (gaps[6] / g7) ** 0.5
        est.update(gap_extrapolated_L7=g7, gap_history=gaps, lobpcg_iterations_history=it_lob, lobpcg_exponent=p_lob, lobpcg_iterations_L7=[it7_lob, it7_lob_hi],
                   chebfsi_block_matvecs_history=cheb, chebfsi_block24_matvecs_L7=[nmv7_lo, nmv7_hi])
        t_lob = [it7_lob * est['lobpcg_block4_s_per_it'], it7_lob_hi * est['lobpcg_block4_s_per_it']]
        t_cheb = [nmv7_lo * est['block24_s'] * 1.15, nmv7_hi * est['block24_s'] * 1.15]   # +15% for Rayleigh-Ritz / orthonormalisation
        est.update(lobpcg_wall_h=[t / 3600 for t in t_lob], chebfsi_block24_wall_h=[t / 3600 for t in t_cheb],
                   lobpcg_block4_ram_gb=HGB7 + 32 * vec7 + 0.5, chebfsi_block24_ram_gb=HGB7 + 4 * 24 * vec7 + 0.5, chebfsi_block16_ram_gb=HGB7 + 4 * 16 * vec7 + 0.5, chebfsi_block8_ram_gb=HGB7 + 4 * 8 * vec7 + 0.5)
        L(f"   gap to the second Kramers pair: stored 2.92e-2 (L4), 1.97e-3 (L5), 1.08e-4 (L6); ratios {gaps[5]/gaps[4]:.4f}, {gaps[6]/gaps[5]:.4f} -> extrapolated L7 gap ~ {g7:.1e}")
        L(f"   LOBPCG block 4 (tol 1e-6): 972 it (L5), 3100 it (L6) [stored logs]; empirical iterations ~ gap^-{p_lob:.2f} (theory -0.5) -> L7: {it7_lob:.0f} - {it7_lob_hi:.0f} iterations = {t_lob[0]/3600:.1f} - {t_lob[1]/3600:.1f} h at {est['lobpcg_block4_s_per_it']:.2f} s/it; RAM ~ {est['lobpcg_block4_ram_gb']:.1f} GB (H + ~32 vectors).")
        alt = 8.0 * 1692.0 / 3100.0; est['lobpcg_block4_s_per_it_from_stored_log_x8'] = alt; est['lobpcg_wall_h_from_stored_log'] = [it7_lob * alt / 3600, it7_lob_hi * alt / 3600]
        L(f"      alternative anchor: the stored L6 log averaged 1692 s / 3100 it = 0.55 s/it (0.25-0.99 s/it as the load varied); x8 -> {alt:.2f} s/it -> {it7_lob*alt/3600:.1f} - {it7_lob_hi*alt/3600:.1f} h.  Timings on this shared machine fluctuate by ~2x.")
        L(f"      caveat: scipy LOBPCG stagnated at residual 3.5e-7 at L6 (and 2.7e-8 at L5), i.e. tol 1e-7 may be unreachable; at the L7 gap {g7:.0e} a residual 1e-6 means an eigenvector angle up to {1e-6/g7:.2f} rad.")
        L(f"   ChebFSI (K=8, block 24, deg <= 150): 1373 block matvecs to res 9e-7 at L6 [stored edge_states log]; (K=4, block 32, deg <= 80): stalled at 2.8e-4 after 488 [stored level6_structure log]; (K=128, block 192): 488 to 1e-8 at L5.")
        L(f"      L7, K=8, block 24: {nmv7_lo:.0f} - {nmv7_hi:.0f} block matvecs x ~{est['block24_s']:.2f} s (+15% RR) = {t_cheb[0]/3600:.1f} - {t_cheb[1]/3600:.1f} h; RAM ~ {est['chebfsi_block24_ram_gb']:.1f} GB (block 16: {est['chebfsi_block16_ram_gb']:.1f} GB, block 8: {est['chebfsi_block8_ram_gb']:.1f} GB).")
        cert5 = 99.0; cert7 = cert5 * 64
        est.update(certification_pure_python_s=cert7, certification_vectorised_s=cert7 / 30)
        L(f"   exact rational certification (Rayleigh quotient of the 2^24-scaled Gaussian-integer rounding, phase5a_certified_upper_bound.py): 99 s at L5 in pure Python -> ~{cert7/3600:.1f} h at L7 (64x work); "
          f"with numpy int64 chunked sums (products < 2^50, partial sums of <= 2^12 terms) ~{cert7/30/60:.0f} min; memory ~ 3 integer vectors of dim 4.2M (< 0.5 GB). It needs the float vector first.")
        out['level7'] = est
    jdump(out, f'{TAG}_scaling.json')
    with open(os.path.join(RES, f'{TAG}_scaling.txt'), 'w') as f: f.write('\n'.join(lines) + '\n')
    say(f"\nsaved audit/results/{TAG}_scaling.txt and .json")

if __name__ == '__main__':
    cmd = sys.argv[1]
    if cmd == 'cost': cost()
    elif cmd == 'solve': solve(sys.argv[2], int(sys.argv[3]), int(sys.argv[4]) if len(sys.argv) > 4 else None)
    elif cmd == 'analyze': analyze()
    else: raise SystemExit(__doc__)
