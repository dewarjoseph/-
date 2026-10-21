#!/usr/bin/env python3
"""
Phase 5a / Task C3: ground-state structure at level 6 -- FR30 Chair44 tiling versus the periodic-geometry (unit-cube)
control that shares the FR30-type decoration hierarchy but not the chair geometry.

Operator (conventions identical to audit/phase5_bulk_bottom_lobpcg.py and audit/phase5a_controls.py):
  Hilbert space l^2(tiles) x C^2; (A psi)_a = sum over shared unit panels f=(a,b) of C_ab psi_b with
  C_ab = (sigma.M_a^T n_f)(sigma.M_b^T n_f) in Q8 and C_ba = C_ab^dagger; panels between the same pair of tiles are
  summed with multiplicity.  FR30 chair: H_pin = 24 I - A (bulk coordination 24).  Unit-cube control: H = 6 I - A
  (bulk coordination 6, FR30-type decoration {v: FR30[v], (1,1,1) -> (0,2,1)} exactly as phase5a_controls.part_cube).
Geometry: vectorized re-implementation (dense owner grid of unit cubes) of tiles_at_level/panel_edges (chair) and of
  phase5a_controls.cube_tiles (cube) with the SAME depth-first tile order, so that tile_index // 8**(L-d) is the depth-d
  ancestor.  At levels <= 5 the sparse operator is cross-validated entry by entry against the object builders
  (independent_clifford_q8_audit.tiles_at_level / panel_edges / clifford_link, phase5a_controls.cube_tiles / build_H).
Solver: dense eigh at level 3 (dim 1024); otherwise LOBPCG with k=2 wanted + 2 guard vectors (block 4), diagonal
  preconditioner, seed 0, tol 1e-6, at most 4000 iterations in total.  LOBPCG runs in chunks of <= 500 iterations, each
  chunk restarted from the current Ritz block (the conjugate direction P is dropped at a restart), which gives progress
  logging and a wall-clock budget; eigenvalues are recomputed as Rayleigh quotients of the normalized Ritz vectors and
  residual norms ||H psi - lambda psi||_2 are reported for every vector of the block.
Ground-state diagnostics (tile density p_a = |psi_a1|^2 + |psi_a2|^2, sum 1, averaged over the Kramers pair; it is the
  same for every unit vector of the pair):  IPR = sum_a p_a^2, IPR*n, P = 1/IPR;  box counting S2(d) = sum over the 8^d
  depth-d children of (weight in child)^2, 1/S2(d) = effective number of occupied depth-d children, local correlation
  dimension D2(d) = log2(S2(d-1)/S2(d)) (3 for a uniform state, S2(0) = 1);  interface weight at depth d = weight on
  tiles incident to a shared panel joining two different depth-d children, with the fraction of such tiles;  boundary
  weight = weight on tiles with degree < bulk coordination;  s50, s90 = number of tiles carrying 50% / 90% of the weight.
Run from the repository root with OMP_NUM_THREADS=1:
  python3 -u -I audit/phase5a_level6_structure.py run fr30 6 [--budget SECONDS]     (also run fr30 3|4|5, run cube 3..6)
  python3 -u -I audit/phase5a_level6_structure.py table
Outputs: audit/results/phase5a_level6_structure_<system>_level<L>.log / .json, ground-state tile weights
  audit/results/phase5a_fr30_level6_groundstate_weights.npy (and phase5a_<system>_level<L>_groundstate_weights.npy),
  merged report audit/results/phase5a_level6_structure.txt and .json.
"""
import os, sys, time, json, argparse, collections, itertools, resource, warnings
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
RES = os.path.join(HERE, 'results')
import numpy as np, scipy.sparse as sps, scipy.sparse.linalg as spl, scipy.linalg as sla
from independent_clifford_q8_audit import FR30, U3, perm_mat, clifford_link, q8label, SIG, tiles_at_level, panel_edges

V8 = list(itertools.product((0, 1), repeat=3))
CUBE_DEC = {v: FR30.get(v, (0, 2, 1)) for v in V8}            # phase5a_controls.part_cube decoration
I2 = np.eye(2, dtype=complex)
Q8_NAMES = ['+1', '-1', '+i', '-i', '+j', '-j', '+k', '-k']
Q8_MATS = {'+1': I2, '-1': -I2}
for k, nm in enumerate('ijk'):
    Q8_MATS['+' + nm] = 1j * SIG[k]; Q8_MATS['-' + nm] = -1j * SIG[k]
SYSTEMS = {'fr30': dict(bulk=24, title='FR30 Chair44 tiling, Q8 Clifford links, pinned diagonal 24'),
           'cube': dict(bulk=6, title='unit-cube block substitution, FR30-type decoration, Q8 Clifford links, pinned diagonal 6')}
QUOTED = {  # IPR*n values quoted in the task context (used in the final table alongside the recomputed ones)
    'fr30': {3: 6.424, 4: 9.146, 5: 20.0, 6: 42.0},
    'cube': {3: 7.836, 4: 10.292}}
QUOTED_NOTE = {'fr30': 'levels 3-4 from phase5a_controls (dense / LOBPCG tol 1e-7); level 5 = 0.00061*32768 and level 6 = 0.00016*262144 from phase5_bulk_bottom_lobpcg (IPR printed with 5 decimals, so +-3% and +-8% quantization)',
               'cube': 'levels 3-4 from phase5a_controls part cube'}

def rss_gb(): return resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 1e6
def conv(o):
    if isinstance(o, np.integer): return int(o)
    if isinstance(o, np.floating): return float(o)
    if isinstance(o, np.ndarray): return o.tolist()
    raise TypeError(str(type(o)))
class Log:
    def __init__(self, path): self.fh = open(path, 'w')
    def __call__(self, msg=''):
        print(msg, flush=True); self.fh.write(msg + '\n'); self.fh.flush()

# ---------------------------------------------------------------- geometry (vectorized, depth-first order)
def Ds(v): return np.diag([1 - 2*v[0], 1 - 2*v[1], 1 - 2*v[2]])
def substitution(system):
    """(opG, opT, base cubes (doubled centres), box side at level L) with the child order of the object builders."""
    if system == 'fr30':
        opG = np.array([perm_mat(FR30['0'])] + [Ds(v) @ perm_mat(FR30[v]) for v in U3], dtype=np.int64)
        opT = np.array([[1, 1, 1]] + [[4*v[0], 4*v[1], 4*v[2]] for v in U3], dtype=np.int64)
        base = np.array([[2*u[0]+1, 2*u[1]+1, 2*u[2]+1] for u in U3], dtype=np.int64)
        return opG, opT, base, (lambda L: 2 ** (L + 1))
    opG = np.array([Ds(v) @ perm_mat(CUBE_DEC[v]) for v in V8], dtype=np.int64)
    opT = np.array([[2*v[0], 2*v[1], 2*v[2]] for v in V8], dtype=np.int64)
    return opG, opT, np.array([[1, 1, 1]], dtype=np.int64), (lambda L: 2 ** L)

def poses(opG, opT, level):
    """Vectorized pose recursion: identical to [(G@g, 2T+G@t) for G,T in poses for g,t in ops] (parent-major order)."""
    Gs = np.eye(3, dtype=np.int64)[None]; Ts = np.zeros((1, 3), dtype=np.int64)
    for _ in range(level):
        Gn = np.einsum('pij,ojk->poik', Gs, opG).reshape(-1, 3, 3)
        Tn = (2 * Ts[:, None, :] + np.einsum('pij,oj->poi', Gs, opT)).reshape(-1, 3)
        Gs, Ts = Gn, Tn
    return Gs, Ts

def build_geometry(system, level, log):
    t0 = time.time(); opG, opT, base, boxside = substitution(system); bulk = SYSTEMS[system]['bulk']
    G, T = poses(opG, opT, level); n = G.shape[0]; nb = base.shape[0]
    cubes = (np.einsum('pij,cj->pci', G, base) + 2 * T[:, None, :] - 1) // 2          # (n, nb, 3) unit-cube corners
    S = boxside(level); assert cubes.min() >= 0 and cubes.max() < S, 'tile outside the box'
    owner = np.full((S, S, S), -1, dtype=np.int32); flat = cubes.reshape(-1, 3)
    owner[flat[:, 0], flat[:, 1], flat[:, 2]] = np.repeat(np.arange(n, dtype=np.int32), nb)
    occ = owner >= 0; assert occ.sum() == nb * n, 'overlapping unit cubes'
    if system == 'fr30':   # the level-L supertile is [0,S)^3 minus the open octant (S/2 .. S)^3
        h = S // 2; expect = np.ones((S, S, S), bool); expect[h:, h:, h:] = False
        assert (occ == expect).all(), 'chair supertile shape violated'
    else:
        assert occ.all(), 'cube control does not fill the box'
    del cubes, flat, occ
    ea, eb, eax = [], [], []
    for ax in range(3):                       # panel between cube c (tile a) and c + e_ax (tile b): normal +e_ax from a to b
        o1 = np.moveaxis(owner, ax, 0)[:-1]; o2 = np.moveaxis(owner, ax, 0)[1:]
        sel = (o1 >= 0) & (o2 >= 0) & (o1 != o2)
        ea.append(o1[sel].astype(np.int64)); eb.append(o2[sel].astype(np.int64)); eax.append(np.full(int(sel.sum()), ax, dtype=np.int64))
    del owner
    ea = np.concatenate(ea); eb = np.concatenate(eb); eax = np.concatenate(eax); E = len(ea)
    keys, fid = np.unique(G.reshape(n, 9), axis=0, return_inverse=True); fid = fid.reshape(-1).astype(np.int64)
    frames = [k.reshape(3, 3) for k in keys]; F = len(frames)
    table = np.empty((F, F, 3), dtype=np.int64)
    for i in range(F):
        for j in range(F):
            for ax in range(3):
                nf = np.zeros(3, dtype=np.int64); nf[ax] = 1
                name = q8label(clifford_link(frames[i], frames[j], nf)); assert name != 'other', 'link not in Q8'
                table[i, j, ax] = Q8_NAMES.index(name)
    lab = table[fid[ea], fid[eb], eax]
    deg = np.bincount(ea, minlength=n) + np.bincount(eb, minlength=n); assert deg.max() == bulk, f'max degree {deg.max()} != {bulk}'
    geo = dict(system=system, level=level, n=n, ea=ea, eb=eb, eax=eax, lab=lab, deg=deg, bulk=bulk, frames=F,
               label_counts={Q8_NAMES[i]: int(c) for i, c in zip(*np.unique(lab, return_counts=True))}, build_s=time.time() - t0)
    log(f"[{system} L{level}] geometry: n={n} tiles ({nb} unit cubes each), box {S}^3, panels |E|={E}, {F} frames, max degree {deg.max()}, "
        f"boundary tiles (deg<{bulk}) {int((deg < bulk).sum())} = {float((deg < bulk).mean()):.4f} n; links {geo['label_counts']}  ({geo['build_s']:.1f}s, rss {rss_gb():.2f} GB)")
    return geo

def build_H(geo, diag_value):
    """Sparse Hermitian H = diag_value I - A (CSR, complex), one 2x2 Q8 block per panel; only the two nonzero entries of each Q8 element are stored."""
    n, E, ea, eb, lab = geo['n'], len(geo['ea']), geo['ea'], geo['eb'], geo['lab']
    rows = [np.arange(2 * n)]; cols = [np.arange(2 * n)]; vals = [np.full(2 * n, float(diag_value), dtype=complex)]
    for li, name in enumerate(Q8_NAMES):
        sel = np.nonzero(lab == li)[0]
        if len(sel) == 0: continue
        C = Q8_MATS[name]; a = ea[sel]; b = eb[sel]
        for r in range(2):
            for c in range(2):
                if C[r, c] != 0:
                    rows.append(2*a + r); cols.append(2*b + c); vals.append(np.full(len(sel), -C[r, c]))
                    rows.append(2*b + c); cols.append(2*a + r); vals.append(np.full(len(sel), -np.conj(C[r, c])))
    rows = np.concatenate(rows).astype(np.int32); cols = np.concatenate(cols).astype(np.int32); vals = np.concatenate(vals)
    H = sps.csr_matrix((vals, (rows, cols)), shape=(2 * n, 2 * n)); del rows, cols, vals
    H.sum_duplicates(); return H

def validate_against_objects(system, level, geo, H, diag_value, log):
    """Entry-by-entry comparison with the object builders (tiles_at_level/panel_edges or cube_tiles) and phase5a_controls.build_H."""
    import phase5a_controls as pc
    t0 = time.time()
    tiles = tiles_at_level(FR30, level) if system == 'fr30' else pc.cube_tiles(CUBE_DEC, level)
    owner, edges = panel_edges(tiles); n = len(tiles); assert n == geo['n']
    Href = pc.build_H(n, edges, pc.clifford_links(tiles, edges), np.full(n, float(diag_value)))
    D = (H - Href); dev = float(np.abs(D.data).max()) if D.nnz else 0.0
    degref = pc.degrees(n, edges)
    log(f"   validation vs object builders (level {level}): |E| {len(edges)} vs {len(geo['ea'])}, max|H_grid - H_objects| = {dev:.1e}, degrees identical: {bool((degref == geo['deg']).all())}  ({time.time()-t0:.1f}s)")
    assert dev == 0.0 and len(edges) == len(geo['ea']) and (degref == geo['deg']).all(), 'grid builder disagrees with object builders'
    return dev

# ---------------------------------------------------------------- solvers
def ritz(H, V):
    V = V / np.linalg.norm(V, axis=0); HV = H @ V
    lam = np.real(np.einsum('ij,ij->j', V.conj(), HV)); res = np.linalg.norm(HV - V * lam, axis=0)
    o = np.argsort(lam); return lam[o], V[:, o], res[o]

def solve_dense(H, k):
    t0 = time.time(); w, V = sla.eigh(H.toarray()); lam, V, res = ritz(H, V[:, :k + 2])
    return dict(method='dense eigh (full spectrum)', lam=lam, V=V, res=res, iterations=None, seconds=time.time() - t0,
                full_lowest8=w[:8].tolist(), converged=True)

def solve_lobpcg(H, k, block, seed, tol, maxiter, chunk, budget, t_start, log):
    N = H.shape[0]; rng = np.random.default_rng(seed)
    X = rng.standard_normal((N, block)) + 1j * rng.standard_normal((N, block))
    dinv = 1.0 / H.diagonal().real
    M = spl.LinearOperator(H.shape, matvec=lambda v: dinv * v, matmat=lambda B: dinv[:, None] * B, dtype=complex)
    it_total = 0; t0 = time.time(); chunks = []; converged = False; stop_reason = None; sec_per_it = None
    while True:
        remaining = maxiter - it_total
        if remaining <= 0: stop_reason = f'maxiter {maxiter} reached'; break
        left = budget - (time.time() - t_start)
        it_this = min(chunk, remaining)
        if sec_per_it is not None:
            it_afford = int((left - 30.0) / sec_per_it)          # keep 30 s for diagnostics and output
            if it_afford < 20: stop_reason = f'wall-clock budget {budget:.0f}s exhausted'; break
            it_this = min(it_this, it_afford)
        tc = time.time()
        with warnings.catch_warnings(record=True) as wl:
            warnings.simplefilter('always')
            w, V, hist = spl.lobpcg(H, X, M=M, largest=False, tol=tol, maxiter=it_this, retResidualNormsHistory=True)
        n_it = len(hist); it_total += n_it; dt = time.time() - tc; sec_per_it = dt / max(n_it, 1)
        lam, V, res = ritz(H, V); X = V
        chunks.append(dict(iterations=n_it, cumulative=it_total, seconds=dt, lam=lam.tolist(), res=res.tolist(), rss_gb=rss_gb(),
                           warnings=[str(x.message).splitlines()[0][:120] for x in wl]))
        log(f"   lobpcg chunk: {n_it:4d} it ({dt:.0f}s, {sec_per_it:.2f}s/it), cumulative {it_total:5d}: lambda={np.array2string(lam, precision=7, max_line_width=200)} "
            f"res={np.array2string(res, max_line_width=200, formatter={'float_kind': lambda x: f'{x:.1e}'})}  rss {rss_gb():.2f} GB")
        if res.max() < tol: converged = True; stop_reason = f'all {block} block residuals < tol={tol:g}'; break
        if n_it < it_this and res.max() >= tol:    # lobpcg returned early without convergence (internal break)
            if len(chunks) >= 2 and chunks[-1]['iterations'] <= 3: stop_reason = 'lobpcg stalls (returns after <=3 iterations)'; break
    return dict(method=f'lobpcg(block={block}, seed={seed}, tol={tol:g}, maxiter={maxiter}, chunks of <= {chunk} it, warm restart)', lam=lam, V=V, res=res,
                iterations=it_total, seconds=time.time() - t0, converged=converged, stop_reason=stop_reason, chunks=chunks,
                tol=tol, k_wanted_converged=bool(res[:k].max() < tol))

def solve_chebfsi(H, k, m, lam_max, tol, budget, t_start, seed, log):
    """Chebyshev-filtered subspace iteration of audit/phase5a_edge_states.py (validated there against dense eigh at
    level 4 to 5e-14): block m, Zhou-Saad filter on [theta_m, lam_max], Rayleigh-Ritz on the exact operator; the
    lowest 4 Ritz pairs (two Kramers pairs) are returned after a final Rayleigh-quotient/residual evaluation."""
    import phase5a_edge_states as es
    t0 = time.time(); N = H.shape[0]
    th, X, res_all, nmv, hist = es.chebfsi(lambda B: H @ B, N, 4, m, lam_max, tol=tol, max_passes=400, time_budget=max(60.0, budget - (time.time() - t_start) - 60.0),
                                           seed=seed, dtype=complex, logf=log.fh)
    lam, V, res = ritz(H, X[:, :4]); del X
    conv = bool(res[:4].max() < tol)
    return dict(method=f'chebfsi(block={m}, K=4, lam_max={lam_max}, tol={tol:g}, seed={seed}; Zhou-Saad Chebyshev filter + Rayleigh-Ritz, audit/phase5a_edge_states.py)',
                lam=lam, V=V, res=res, iterations=int(nmv), seconds=time.time() - t0, converged=conv, stop_reason=('res[:4] < tol' if conv else 'time budget / pass limit'),
                chunks=hist, tol=tol, k_wanted_converged=bool(res[:k].max() < tol), ritz_all=th.tolist(), res_all=res_all.tolist())

# ---------------------------------------------------------------- diagnostics
def tile_density(v):
    p = np.abs(v[0::2])**2 + np.abs(v[1::2])**2; return p / p.sum()

def diagnostics(p, geo):
    L, n, ea, eb = geo['level'], geo['n'], geo['ea'], geo['eb']
    ipr = float((p**2).sum()); ps = np.sort(p)[::-1]; cum = np.cumsum(ps)
    out = dict(n=n, ipr=ipr, ipr_n=ipr * n, P=1.0 / ipr, p_max=float(ps[0]), s50=int(np.searchsorted(cum, 0.5) + 1), s90=int(np.searchsorted(cum, 0.9) + 1),
               boundary_weight=float(p[geo['deg'] < geo['bulk']].sum()), boundary_tile_fraction=float((geo['deg'] < geo['bulk']).mean()),
               S2={}, inv_S2={}, D2={}, child_weights_depth1=None, interface_weight={}, interface_tile_fraction={}, interface_tiles={}, interface_enhancement={})
    prev = 1.0
    for d in range(1, L + 1):
        W = p.reshape(8**d, 8**(L - d)).sum(axis=1)                 # depth-first order: tiles of one depth-d child are contiguous
        s2 = float((W**2).sum()); out['S2'][d] = s2; out['inv_S2'][d] = 1.0 / s2; out['D2'][d] = float(np.log2(prev / s2)); prev = s2
        if d == 1: out['child_weights_depth1'] = [float(x) for x in W]
        if d == 2: out['child_weights_depth2_top8'] = [float(x) for x in np.sort(W)[::-1][:8]]
        q = 8**(L - d); cross = (ea // q) != (eb // q)
        m = np.zeros(n, dtype=bool); m[ea[cross]] = True; m[eb[cross]] = True
        iw = float(p[m].sum()); fr = float(m.mean())
        out['interface_weight'][d] = iw; out['interface_tile_fraction'][d] = fr; out['interface_tiles'][d] = int(m.sum()); out['interface_enhancement'][d] = iw / fr
    return out

def report_diag(st, log):
    L = max(st['S2']); n = st['n']
    log(f"   ground state: tile IPR={st['ipr']:.6g}  IPR*n={st['ipr_n']:.4f}  P=1/IPR={st['P']:.1f}  p_max={st['p_max']:.3g}  s50={st['s50']} ({st['s50']/n:.4f} n)  s90={st['s90']} ({st['s90']/n:.4f} n)")
    log(f"   boundary weight (deg < bulk) = {st['boundary_weight']:.5f}  (boundary tile fraction {st['boundary_tile_fraction']:.4f}, enhancement {st['boundary_weight']/st['boundary_tile_fraction']:.3f})")
    log(f"   {'d':>2} {'8^d':>7} {'S2(d)':>11} {'1/S2(d)':>10} {'1/S2/8^d':>9} {'D2(d)':>6} | {'interface w(d)':>14} {'tiles':>8} {'fraction':>8} {'w/frac':>7}")
    for d in range(1, L + 1):
        log(f"   {d:2d} {8**d:7d} {st['S2'][d]:11.6g} {st['inv_S2'][d]:10.3f} {st['inv_S2'][d]/8**d:9.4f} {st['D2'][d]:6.3f} | {st['interface_weight'][d]:14.5f} {st['interface_tiles'][d]:8d} {st['interface_tile_fraction'][d]:8.4f} {st['interface_enhancement'][d]:7.3f}")
    log(f"   depth-1 child weights (depth-first child order): {np.array2string(np.array(st['child_weights_depth1']), precision=4, max_line_width=200)}")

# ---------------------------------------------------------------- run one system / level
def run(system, level, block, tol, maxiter, chunk, budget, seed, validate, solver='lobpcg', cheb_block=32, tag_suffix=''):
    T0 = time.time(); tag = f'phase5a_level6_structure_{system}_level{level}' + (f'_{tag_suffix}' if tag_suffix else '')
    log = Log(os.path.join(RES, tag + '.log')); diag_value = SYSTEMS[system]['bulk']
    log(f"=== {SYSTEMS[system]['title']}: level {level} ===  (started {time.strftime('%Y-%m-%d %H:%M:%S')}, OMP_NUM_THREADS={os.environ.get('OMP_NUM_THREADS')})")
    geo = build_geometry(system, level, log)
    t1 = time.time(); H = build_H(geo, diag_value)
    herm = (H - H.getH()); herm_dev = float(np.abs(herm.data).max()) if herm.nnz else 0.0; del herm
    log(f"   H = {diag_value} I - A: dim {H.shape[0]}, nnz {H.nnz}, max|H - H^dagger| = {herm_dev:.1e}  ({time.time()-t1:.1f}s, rss {rss_gb():.2f} GB)")
    assert herm_dev == 0.0
    val_dev = validate_against_objects(system, level, geo, H, diag_value, log) if (validate and level <= 5) else None
    k = 2
    if level <= 3: sol = solve_dense(H, k)
    elif solver == 'chebfsi': sol = solve_chebfsi(H, k, cheb_block, 2.0 * diag_value, tol, budget, T0, seed, log)
    else: sol = solve_lobpcg(H, k, block, seed, tol, maxiter, chunk, budget, T0, log)
    lam, V, res = sol['lam'], sol['V'], sol['res']
    log(f"   solver: {sol['method']}  iterations={sol['iterations']}  ({sol['seconds']:.0f}s)  converged={sol['converged']}" + (f"  stop: {sol['stop_reason']}" if sol.get('stop_reason') else ''))
    log(f"   lowest eigenvalues (Rayleigh quotients): {np.array2string(lam, precision=7, max_line_width=200)}")
    log(f"   residuals ||H psi - lambda psi||:        {np.array2string(res, precision=2, max_line_width=200)}")
    log(f"   Kramers split lambda_2 - lambda_1 = {lam[1]-lam[0]:.2e};  gap to next pair lambda_3 - lambda_1 = {lam[2]-lam[0]:.3e};  eigenvector angle bound res_1/gap = {res[0]/max(lam[2]-lam[0],1e-300):.1e}")
    p1 = tile_density(V[:, 0]); p2 = tile_density(V[:, 1]); p = 0.5 * (p1 + p2)
    st = diagnostics(p, geo); st['ipr_vec1'] = float((p1**2).sum()); st['ipr_vec2'] = float((p2**2).sum())
    st['pair_density_max_diff'] = float(np.abs(p1 - p2).max())
    log(f"   Kramers pair check: IPR vec1 {st['ipr_vec1']:.6g}, vec2 {st['ipr_vec2']:.6g}, max_a |p1_a - p2_a| = {st['pair_density_max_diff']:.1e}")
    report_diag(st, log)
    # second Kramers pair (block vectors 3,4) for comparison
    if V.shape[1] >= 4 and res[2] < 1e-3:
        p3 = 0.5 * (tile_density(V[:, 2]) + tile_density(V[:, 3])); st2 = diagnostics(p3, geo)
        log(f"   second pair (lambda={lam[2]:.7f}, res {res[2]:.1e}): IPR*n={st2['ipr_n']:.4f} s50={st2['s50']} s90={st2['s90']} 1/S2(d)={[round(st2['inv_S2'][d],2) for d in range(1, level+1)]} interface w(1)={st2['interface_weight'][1]:.4f}")
    else: st2 = None
    wpath = os.path.join(RES, f'phase5a_{system}_level{level}_groundstate_weights' + (f'_{tag_suffix}' if tag_suffix else '') + '.npy'); np.save(wpath, p)
    rec = dict(system=system, title=SYSTEMS[system]['title'], level=level, n=geo['n'], dim=int(H.shape[0]), n_edges=int(len(geo['ea'])), nnz=int(H.nnz),
               diag=diag_value, bulk=geo['bulk'], label_counts=geo['label_counts'], hermiticity_dev=herm_dev, validation_max_dev=val_dev,
               solver=sol['method'], iterations=sol['iterations'], solver_seconds=sol['seconds'], converged=sol['converged'], stop_reason=sol.get('stop_reason'),
               k_wanted_converged=sol.get('k_wanted_converged', True), eigenvalues=lam.tolist(), residuals=res.tolist(), kramers_split=float(lam[1] - lam[0]),
               gap_to_next_pair=float(lam[2] - lam[0]), full_lowest8=sol.get('full_lowest8'), chunks=sol.get('chunks'), ground=st, second_pair=st2,
               weights_file=os.path.relpath(wpath, os.path.dirname(HERE)), total_seconds=time.time() - T0, max_rss_gb=rss_gb(), quoted_ipr_n=QUOTED[system].get(level),
               tag=tag_suffix or 'lobpcg', ritz_all=sol.get('ritz_all'), res_all=sol.get('res_all'))
    with open(os.path.join(RES, tag + '.json'), 'w') as fh: json.dump(rec, fh, indent=1, default=conv)
    log(f"   saved {os.path.relpath(wpath, os.path.dirname(HERE))} and {tag}.json;  total {rec['total_seconds']:.0f}s, max rss {rec['max_rss_gb']:.2f} GB")
    return rec

# ---------------------------------------------------------------- merged table
def table():
    import glob
    log = Log(os.path.join(RES, 'phase5a_level6_structure.txt'))
    recs, allrecs = {}, {}
    for system in SYSTEMS:
        for L in range(3, 7):
            rs = [json.load(open(f)) for f in sorted(glob.glob(os.path.join(RES, f'phase5a_level6_structure_{system}_level{L}*.json')))]
            if not rs: continue
            allrecs[(system, L)] = rs
            # primary record: converged with the smallest ground-state residual; otherwise the smallest residual
            conv = [r for r in rs if r['k_wanted_converged']] or rs
            recs[(system, L)] = min(conv, key=lambda r: r['residuals'][0])
    log("PHASE 5a / TASK C3 -- LEVEL-6 GROUND-STATE STRUCTURE: FR30 CHAIR VERSUS THE PERIODIC-GEOMETRY (UNIT-CUBE) CONTROL")
    log("All numbers below are numerical results of this script (ground state = lowest Kramers pair of the pinned operator); residuals are ||H psi - lambda psi||_2.")
    log(__doc__.split('Run from the repository root')[0])
    log("0. SOLVER RECORDS PER (system, level) -- the primary record (marked *) is the converged one with the smallest ground-state residual")
    for (system, L), rs in sorted(allrecs.items()):
        for r in rs:
            mark = '*' if r is recs[(system, L)] else ' '
            log(f"  {mark} {system} L{L} [{r.get('tag','lobpcg')}] {r['solver'][:60]:<60} it={r['iterations']} {r['solver_seconds']:.0f}s rss={r['max_rss_gb']:.2f}GB conv={r['converged']} (wanted pair conv={r['k_wanted_converged']}) "
                f"lambda_1={r['eigenvalues'][0]:.7f} res_1={r['residuals'][0]:.1e} IPR*n={r['ground']['ipr_n']:.4f} s50={r['ground']['s50']} 1/S2(1)={r['ground']['inv_S2']['1']:.3f}" + (f"  stop: {r['stop_reason']}" if r.get('stop_reason') else ''))
        if len(rs) >= 2:
            a, b = rs[0], rs[1]
            log(f"    cross-check {a.get('tag')} vs {b.get('tag')}: |d lambda_1| = {abs(a['eigenvalues'][0]-b['eigenvalues'][0]):.1e}, |d lambda_3| = {abs(a['eigenvalues'][2]-b['eigenvalues'][2]):.1e}, |d IPR*n| = {abs(a['ground']['ipr_n']-b['ground']['ipr_n']):.2e}, "
                f"|d 1/S2(1)| = {abs(a['ground']['inv_S2']['1']-b['ground']['inv_S2']['1']):.2e}, |d interface w(1)| = {abs(a['ground']['interface_weight']['1']-b['ground']['interface_weight']['1']):.2e}, s50 {a['ground']['s50']} vs {b['ground']['s50']}")
            try:
                wa = np.load(os.path.join(os.path.dirname(HERE), a['weights_file'])); wb = np.load(os.path.join(os.path.dirname(HERE), b['weights_file']))
                log(f"    tile-density difference max_a |p_a - p'_a| = {np.abs(wa-wb).max():.2e}, L1 = {np.abs(wa-wb).sum():.2e}")
            except Exception as ex: log(f"    (weights comparison skipped: {ex})")
    log("\n1. PER-LEVEL RESULTS (primary records)")
    hdr = f"{'system':<6} {'L':>1} {'n':>7} {'dim':>7} {'lambda_min':>11} {'resid':>8} {'gap pair2':>9} {'IPR*n':>8} {'quoted':>7} {'P':>8} {'s50':>6} {'s90':>7} {'bw':>8} {'solver':<22} {'it':>5} {'s':>6} {'GB':>5}"
    log(hdr); log('-' * len(hdr))
    for (system, L), r in sorted(recs.items()):
        g = r['ground']; q = r.get('quoted_ipr_n')
        log(f"{system:<6} {L:>1} {r['n']:>7} {r['dim']:>7} {r['eigenvalues'][0]:11.6f} {r['residuals'][0]:8.1e} {r['gap_to_next_pair']:9.2e} {g['ipr_n']:8.3f} {q if q is not None else '-':>7} {g['P']:8.1f} {g['s50']:6d} {g['s90']:7d} {g['boundary_weight']:8.5f} "
            f"{r['solver'][:22]:<22} {str(r['iterations']) if r['iterations'] is not None else '-':>5} {r['solver_seconds']:6.0f} {r['max_rss_gb']:5.2f}"
            + ('' if r['converged'] else f"   NOT CONVERGED ({r.get('stop_reason')})"))
    log("\n   lowest 4 eigenvalues and residuals:")
    for (system, L), r in sorted(recs.items()):
        log(f"   {system} L{L}: lambda = {np.array2string(np.array(r['eigenvalues']), precision=7, max_line_width=200)}  res = {np.array2string(np.array(r['residuals']), precision=1, max_line_width=200)}")
    log("\n2. BOX COUNTING: 1/S2(d) = effective number of occupied depth-d children (8^d children; uniform state gives 8^d), D2(d) = log2(S2(d-1)/S2(d)) (uniform 3)")
    for (system, L), r in sorted(recs.items()):
        g = r['ground']
        log(f"   {system} L{L} (n={r['n']}): 1/S2(d) d=1..{L}: " + '  '.join(f"{g['inv_S2'][str(d)]:.3f}" for d in range(1, L + 1))
            + "   | occupied fraction 1/S2/8^d: " + ' '.join(f"{g['inv_S2'][str(d)]/8**d:.3f}" for d in range(1, L + 1))
            + "   | D2(d): " + ' '.join(f"{g['D2'][str(d)]:.2f}" for d in range(1, L + 1)))
    log("\n3. INTERFACE WEIGHTS: weight on tiles incident to a panel joining two different depth-d children / fraction of such tiles (enhancement = ratio)")
    for (system, L), r in sorted(recs.items()):
        g = r['ground']
        log(f"   {system} L{L}: " + '  '.join(f"d{d}: {g['interface_weight'][str(d)]:.4f}/{g['interface_tile_fraction'][str(d)]:.4f} ({g['interface_enhancement'][str(d)]:.2f})" for d in range(1, L + 1)))
    log("\n4. GROWTH OF IPR*n WITH LEVEL (n = 8^L tiles).  Two-point exponents between consecutive levels: beta = log(IPR*n ratio)/log 8 (IPR*n ~ n^beta), gamma = 1 - beta (IPR ~ n^-gamma; extended gamma=1, localized gamma=0)")
    growth = {}
    for system in SYSTEMS:
        comp = {L: recs[(system, L)]['ground']['ipr_n'] for L in range(3, 7) if (system, L) in recs}
        quoted = QUOTED[system]
        log(f"   {system}: computed IPR*n: " + ', '.join(f"L{L}: {v:.3f}" for L, v in sorted(comp.items())) + f"   | quoted in task context: " + ', '.join(f"L{L}: {v}" for L, v in sorted(quoted.items())) + f"   ({QUOTED_NOTE[system]})")
        rows = []
        for L in range(3, 6):
            if L in comp and L + 1 in comp:
                ratio = comp[L + 1] / comp[L]; beta = float(np.log(ratio) / np.log(8)); rows.append(dict(levels=[L, L + 1], source='computed', ratio=ratio, beta=beta, gamma=1 - beta))
                log(f"      computed  {L}->{L+1}: IPR*n {comp[L]:.3f} -> {comp[L+1]:.3f}  ratio {ratio:.3f}  beta={beta:.3f}  gamma={1-beta:.3f}")
        merged = dict(quoted); merged.update(comp)      # computed values take precedence where available
        for L in range(3, 6):
            if L in merged and L + 1 in merged and not (L in comp and L + 1 in comp):
                ratio = merged[L + 1] / merged[L]; beta = float(np.log(ratio) / np.log(8)); rows.append(dict(levels=[L, L + 1], source='mixed computed/quoted', ratio=ratio, beta=beta, gamma=1 - beta))
                log(f"      computed+quoted {L}->{L+1}: IPR*n {merged[L]:.3f} -> {merged[L+1]:.3f}  ratio {ratio:.3f}  beta={beta:.3f}  gamma={1-beta:.3f}")
        growth[system] = dict(computed=comp, quoted=quoted, two_point=rows)
    log("\n5. GROWTH OF 1/S2(d) WITH DEPTH d INSIDE THE LEVEL-6 (AND LEVEL-5) STATES: two-point exponent per depth step, log8(1/S2(d+1) / 1/S2(d)) = D2(d+1)/3 (1 = space filling)")
    for (system, L), r in sorted(recs.items()):
        if L < 5: continue
        g = r['ground']
        log(f"   {system} L{L}: " + '  '.join(f"d{d}->{d+1}: {np.log(g['inv_S2'][str(d+1)]/g['inv_S2'][str(d)])/np.log(8):.3f}" for d in range(1, L)))
    log("\n6. SAME-n COMPARISON (FR30 chair vs cube control at equal tile number)")
    for L in range(3, 7):
        if ('fr30', L) in recs and ('cube', L) in recs:
            a = recs[('fr30', L)]['ground']; b = recs[('cube', L)]['ground']
            log(f"   L{L} n={8**L}: IPR*n FR30 {a['ipr_n']:.3f} vs cube {b['ipr_n']:.3f} (ratio {a['ipr_n']/b['ipr_n']:.3f});  s50 {a['s50']} vs {b['s50']};  s90 {a['s90']} vs {b['s90']};  "
                f"1/S2(1) {a['inv_S2']['1']:.3f} vs {b['inv_S2']['1']:.3f};  1/S2(2) {a['inv_S2']['2']:.3f} vs {b['inv_S2']['2']:.3f};  interface w(1) {a['interface_weight']['1']:.4f} vs {b['interface_weight']['1']:.4f};  bw {a['boundary_weight']:.4f} vs {b['boundary_weight']:.4f}")
    with open(os.path.join(RES, 'phase5a_level6_structure.json'), 'w') as fh:
        json.dump(dict(primary={f'{s}_L{L}': {k: v for k, v in r.items() if k != 'chunks'} for (s, L), r in recs.items()},
                       all_records={f'{s}_L{L}': [{k: v for k, v in r.items() if k != 'chunks'} for r in rs] for (s, L), rs in allrecs.items()}, growth=growth), fh, indent=1, default=conv)
    log("\nsaved audit/results/phase5a_level6_structure.json")

if __name__ == '__main__':
    ap = argparse.ArgumentParser(); ap.add_argument('mode', choices=['run', 'table'])
    ap.add_argument('system', nargs='?', choices=list(SYSTEMS)); ap.add_argument('level', nargs='?', type=int)
    ap.add_argument('--block', type=int, default=4); ap.add_argument('--tol', type=float, default=1e-6); ap.add_argument('--maxiter', type=int, default=4000)
    ap.add_argument('--chunk', type=int, default=500); ap.add_argument('--budget', type=float, default=2820.0, help='wall-clock budget in seconds for the whole run (default 47 min)')
    ap.add_argument('--seed', type=int, default=0); ap.add_argument('--no-validate', action='store_true')
    ap.add_argument('--solver', choices=['lobpcg', 'chebfsi'], default='lobpcg'); ap.add_argument('--cheb-block', type=int, default=32)
    ap.add_argument('--tag', default='', help='suffix for the output files (e.g. chebfsi), to keep several solver runs side by side')
    a = ap.parse_args()
    if a.mode == 'table': table()
    else:
        assert a.system and a.level, 'run needs system and level'
        run(a.system, a.level, a.block, a.tol, a.maxiter, a.chunk, a.budget, a.seed, not a.no_validate, solver=a.solver, cheb_block=a.cheb_block, tag_suffix=a.tag)
