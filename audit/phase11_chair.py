#!/usr/bin/env python3
"""Phase XI: an INDEPENDENT re-implementation of the Chair44 objects used by the Phase X certificates.

Nothing here imports the Phase V-X builders (phase5*/phase7*/phase9_pair/phase10_*); everything is re-derived from the written
definitions (deliverables/PHASE7_DEFINITIONS.md sections 1-5).  The Phase X code is used only in tests, to compare outputs.

  geometry   chair = cubes u in {0,1}^3 minus (1,1,1); tile (G, T) owns the cubes (G(2u+1) + 2T - 1)/2; centroid T + (13/14) G(1,1,1)
  sigma      children of (G, T): centre (G P(pi_0), 2T + G(1,1,1)); octant v: (G D_{1-2v} P(pi_v), 2T + 4 G v)
  links      U(a -> b) across a panel with normal e_k = (sigma . M_a^T e_k)(sigma . M_b^T e_k)   (M^T e_k = row k of M)
  operator   pinned H = 24 - A_U on a finite tile set (the compression of the hull operator), free = Deg - A_U
  1-star     the tiles owning a cube at Chebyshev distance <= 1 from a cube of t; its type = sorted relative poses
             (G_t^T G_b, G_t^T (T_b - T_t))
  Phi        1-star types of the 8 children of the central tile, read inside sigma(1-star); the closure lemma (each child's
             1-star is complete inside sigma(tau)) is asserted every time
  balls      B_t = {a : |x_a - x_t| < R} for the tiles t of the central level-m supertile of sigma^m(tau); a ball is accepted only
             when every cube whose centre is within R + sqrt(3)/2 of x_t is owned inside the patch (then no tile of any tiling
             containing the patch can have its centroid within R of x_t: a centroid lies in one of its tile's cubes, within
             (3/7) sqrt 3 < sqrt(3)/2 of that cube's centre)
  IMS        amplified operator 24 - A~, A~_ab = A_ab / c(|x_a - x_b| / rho), rho = R - 311/175, c = overlap of the Dirichlet ground
             state of the unit 3-ball (c_overlap; checked against direct quadrature in tests)
  certificate  banded Cholesky (LAPACK dpbtrf via scipy) of the interleaved real form of (24 - A~) - mu after a reverse
             Cuthill-McKee ordering; Higham (2002) Thm 10.3: lambda_min >= mu - gamma_{N+1} ||L||_F^2 (1 + 2Ku), with a two-ulp
             unit u = 2^-52, minus the entrywise error of the rounded amplification factors.
Usage (CLI): python -u -I audit/phase11_chair.py cert <rule> <R> <m> <nproc> <mu> [tag]
  <rule> = census index (proper), or x<j> (extended index j), -> audit/results/phase11_cert.jsonl"""
import os, sys, json, time, math, itertools, types
from fractions import Fraction
sys.modules.setdefault('resource', types.SimpleNamespace(getrusage=lambda *a: types.SimpleNamespace(ru_maxrss=0), RUSAGE_SELF=0))
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); RES = os.path.join(HERE, 'results')
import numpy as np, scipy.sparse as sps, scipy.linalg as sl
T0 = time.time()
def log(*a): print(f"[{time.time()-T0:7.0f}s]", *a, flush=True)

# ------------------------------------------------------------------ decorations
U3 = [v for v in itertools.product((0, 1), repeat=3) if v != (1, 1, 1)]
PERMS = list(itertools.permutations(range(3)))
def perm_matrix(p):
    M = np.zeros((3, 3), dtype=np.int64); M[np.arange(3), list(p)] = 1; return M
def perm_sign(p): return int(round(np.linalg.det(perm_matrix(p))))
EVEN = [p for p in PERMS if perm_sign(p) == 1]; ODD = [p for p in PERMS if perm_sign(p) == -1]
def proper_decoration(i):
    """census index i (base-3 digits; digit 0 the centre (even permutations), digit k the octant U3[k-1], with the parity that
    makes the frame D_{1-2v} P(pi) proper)"""
    d = [(i // 3 ** k) % 3 for k in range(8)]
    out = [EVEN[d[0]]] + [(EVEN if sum(v) % 2 == 0 else ODD)[d[k + 1]] for k, v in enumerate(U3)]
    return tuple(out)
def extended_decoration(j):
    """extended index j = sum_c d_c 6^c, d_c indexing itertools.permutations(range(3)); c = 0 centre, c >= 1 octant U3[c-1]"""
    return tuple(PERMS[(j // 6 ** c) % 6] for c in range(8))
def rule(spec):
    spec = str(spec)
    return extended_decoration(int(spec[1:])) if spec.startswith('x') else proper_decoration(int(spec))
def child_ops(dec):
    """(frame factor h_c, translation t_c) for the 8 children; child of (G, T) is (G h_c, 2T + G t_c)"""
    h = [perm_matrix(dec[0])] + [np.diag([1 - 2 * x for x in v]) @ perm_matrix(dec[k + 1]) for k, v in enumerate(U3)]
    t = [np.array([1, 1, 1])] + [4 * np.array(v) for v in U3]
    return np.array(h, dtype=np.int64), np.array(t, dtype=np.int64)
def inflate(G, T, dec):
    h, t = child_ops(dec)
    return (np.einsum('nij,cjk->ncik', G, h).reshape(-1, 3, 3), (2 * T[:, None, :] + np.einsum('nij,cj->nci', G, t)).reshape(-1, 3))
def supertile(dec, L):
    G = np.eye(3, dtype=np.int64)[None]; T = np.zeros((1, 3), dtype=np.int64)
    for _ in range(L): G, T = inflate(G, T, dec)
    return G, T

# ------------------------------------------------------------------ geometry
UCUBES = np.array([[2 * a + 1, 2 * b + 1, 2 * c + 1] for a, b, c in U3], dtype=np.int64)
STAR_OFF = np.array([o for o in itertools.product(range(-1, 3), repeat=3) if o != (2, 2, 2)], dtype=np.int64)
def cubes(G, T):
    """(n, 7, 3) integer cubes of the tiles"""
    return (np.einsum('nij,uj->nui', G, UCUBES) + 2 * T[:, None, :] - 1) // 2
def centroid14(G, T):
    """14 x centroid (integer): 14 T + 13 G (1,1,1)"""
    return 14 * T + 13 * G.sum(-1)

class Patch:
    """a finite set of tiles with an owner map on its cubes"""
    def __init__(self, G, T):
        self.G, self.T, self.n = G, T, len(G)
        C = cubes(G, T); self.lo = C.reshape(-1, 3).min(0); C = C - self.lo
        self.shape = tuple(C.reshape(-1, 3).max(0) + 1)
        self.grid = -np.ones(self.shape, dtype=np.int64)
        flat = C.reshape(-1, 3)
        assert (self.grid[tuple(flat.T)] == -1).all()
        self.grid[tuple(flat.T)] = np.repeat(np.arange(self.n), 7)
        assert (self.grid >= 0).sum() == 7 * self.n, 'overlapping tiles'
    def owner(self, q):
        """owner of global cubes q (..., 3); -1 outside"""
        q = q - self.lo; ok = ((q >= 0) & (q < np.array(self.shape))).all(-1); out = -np.ones(q.shape[:-1], dtype=np.int64)
        out[ok] = self.grid[tuple(q[ok].T)]; return out
    def panels(self):
        """(a, b, k): one row per pair of face-adjacent cubes q, q + e_k owned by different tiles a, b"""
        A, B, K = [], [], []
        for k in range(3):
            g = np.moveaxis(self.grid, k, 0); x = g[:-1].ravel(); y = g[1:].ravel(); m = (x >= 0) & (y >= 0) & (x != y)
            A.append(x[m]); B.append(y[m]); K.append(np.full(m.sum(), k))
        return np.concatenate(A), np.concatenate(B), np.concatenate(K)

PAULI = np.array([[[0, 1], [1, 0]], [[0, -1j], [1j, 0]], [[1, 0], [0, -1]]], dtype=complex)
def sigma_dot(rows):
    """sigma . v for signed unit vectors v (..., 3)"""
    k = np.abs(rows).argmax(-1); s = np.take_along_axis(rows, k[..., None], -1)[..., 0]
    assert (np.abs(rows).sum(-1) == 1).all()
    return s[..., None, None] * PAULI[k]
def link_matrices(G, a, b, k):
    """U(a -> b) = (sigma . M_a^T e_k)(sigma . M_b^T e_k); M^T e_k is row k of M"""
    ra = G[a, k, :]; rb = G[b, k, :]
    return np.einsum('nij,njk->nik', sigma_dot(ra), sigma_dot(rb))

def hermitian(n, a, b, U, diag, scale=None):
    """diag - sum_panels (U(a->b) e_a e_b^+ + h.c.) as a complex CSR matrix of size 2n; scale multiplies each panel's link"""
    if scale is not None: U = U * scale[:, None, None]
    r = np.concatenate([2 * a[:, None] + np.array([0, 0, 1, 1]), 2 * b[:, None] + np.array([0, 0, 1, 1])]).ravel()
    c = np.concatenate([2 * b[:, None] + np.array([0, 1, 0, 1]), 2 * a[:, None] + np.array([0, 1, 0, 1])]).ravel()
    v = np.concatenate([U.reshape(-1, 4), np.conj(np.transpose(U, (0, 2, 1))).reshape(-1, 4)]).ravel()
    A = sps.csr_matrix((-v, (r, c)), shape=(2 * n, 2 * n)); A.sum_duplicates()
    return (A + sps.diags(np.repeat(np.asarray(diag, dtype=float) * np.ones(n), 2))).tocsr()

def operators(G, T, free=False):
    P = Patch(G, T); a, b, k = P.panels(); U = link_matrices(G, a, b, k)
    deg = np.bincount(a, minlength=P.n) + np.bincount(b, minlength=P.n)
    return hermitian(P.n, a, b, U, deg if free else 24)

# ------------------------------------------------------------------ 1-star types and Phi-closure
def star_members(P, t):
    """sorted owner list of the 63 cubes at Chebyshev distance <= 1 from tile t (None if incomplete in P)"""
    G, T = P.G[t], P.T[t]
    q = (np.einsum('ij,oj->oi', G, 2 * STAR_OFF + 1) + 2 * T - 1) // 2
    own = P.owner(q)
    if (own < 0).any(): return None
    return sorted(set(own.tolist()))
def type_key(G, T, mem, t):
    Gt = G[t]
    return tuple(sorted((tuple((Gt.T @ G[b]).ravel().tolist()), tuple((Gt.T @ (T[b] - T[t])).tolist())) for b in mem))
def phi(G, T, c, dec):
    """the 1-stars of the 8 children of the central tile c, read inside sigma(patch); asserts the closure lemma"""
    Gi, Ti = inflate(G, T, dec); P = Patch(Gi, Ti); out = []
    for tt in range(8 * c, 8 * c + 8):
        mem = star_members(P, tt); assert mem is not None, 'closure lemma violated'
        out.append((type_key(Gi, Ti, mem, tt), Gi[mem], Ti[mem], mem.index(tt)))
    return out
def legal_types(dec, L0=5):
    """1-star types of the level-L0 supertile, closed under Phi.  Returns ({key: (G, T, centre)}, number found in T_L0, Phi map)"""
    G, T = supertile(dec, L0); P = Patch(G, T); types_ = {}
    for t in range(P.n):
        mem = star_members(P, t)
        if mem is None: continue
        k = type_key(G, T, mem, t)
        if k not in types_: types_[k] = (G[mem], T[mem], mem.index(t))
    n0 = len(types_); keys = list(types_); i = 0; phimap = {}
    while i < len(keys):
        G1, T1, c = types_[keys[i]]; img = []
        for k, Gc, Tc, cc in phi(G1, T1, c, dec):
            if k not in types_: types_[k] = (Gc, Tc, cc); keys.append(k)
            img.append(k)
        phimap[keys[i]] = img; i += 1
    return types_, n0, phimap

def frame_graph(dec):
    """reachable frames from I under g -> g h_c and the period/primitivity of the frame substitution digraph"""
    h, _ = child_ops(dec); key = lambda M: tuple(M.ravel().tolist())
    frames = {key(np.eye(3, dtype=np.int64)): np.eye(3, dtype=np.int64)}; todo = [np.eye(3, dtype=np.int64)]
    while todo:
        g = todo.pop()
        for hc in h:
            gh = g @ hc
            if key(gh) not in frames: frames[key(gh)] = gh; todo.append(gh)
    idx = {k: i for i, k in enumerate(frames)}; n = len(frames); M = np.zeros((n, n), dtype=np.int64)
    for kk, g in frames.items():
        for hc in h: M[idx[key(g @ hc)], idx[kk]] += 1
    # strong connectivity and period via BFS levels
    reach = np.minimum(M + np.eye(n, dtype=np.int64), 1)              # boolean transitive closure (no integer overflow)
    for _ in range(n): reach = np.minimum(reach @ reach, 1)
    irreducible = bool((reach > 0).all())
    lev = {0: 0}; frontier = [0]; per = 0
    while frontier:
        nxt = []
        for u in frontier:
            for v in np.nonzero(M[:, u])[0]:
                v = int(v)
                if v not in lev: lev[v] = lev[u] + 1; nxt.append(v)
                else: per = math.gcd(per, lev[u] + 1 - lev[v])
        frontier = nxt
    P_ = np.eye(n, dtype=np.int64); prim = None
    for kk in range(1, 2 * n * n):
        P_ = np.minimum(P_ @ M, 1)
        if (P_ > 0).all(): prim = kk; break
    return {'frames': n, 'irreducible': irreducible, 'period': per, 'primitive_power': prim,
            'dets': sorted(set(int(round(np.linalg.det(g))) for g in frames.values()))}

# ------------------------------------------------------------------ IMS overlap function
def c_overlap(eta, dps=50):
    """c(eta) = int phi(y) phi(y - eta e) dy / int phi^2, phi = Dirichlet ground state of the unit 3-ball (sin(pi r)/r)"""
    import mpmath as mp
    mp.mp.dps = dps; e = mp.mpf(eta.numerator) / eta.denominator if isinstance(eta, Fraction) else mp.mpf(eta); pi = mp.pi
    return (pi * (1 - e / 2) * mp.sin(pi * e) + 1 - mp.cos(pi * e)) / (pi ** 2 * e)
def c_overlap_quadrature(eta, n=400):
    """direct numerical overlap, for checking c_overlap: radial-axial quadrature of phi(|y|) phi(|y - eta e_z|) over the unit ball"""
    from scipy import integrate
    phi_ = lambda r: np.where(r < 1, np.sinc(r), 0.0)          # sin(pi r)/(pi r)
    f = lambda z, rho_: 2 * np.pi * rho_ * phi_(np.hypot(rho_, z)) * phi_(np.hypot(rho_, z - eta))
    num, _ = integrate.dblquad(lambda rho_, z: f(z, rho_), -1, 1, 0, lambda z: math.sqrt(max(0.0, 1 - z * z)), epsabs=1e-12, epsrel=1e-10)
    den, _ = integrate.quad(lambda r: 4 * np.pi * r * r * float(phi_(np.array(r))) ** 2, 0, 1, epsabs=1e-13)
    return num / den

RC_BOUND = Fraction(311, 175)      # >= r_c = sqrt(619)/14, the largest distance from a tile's centroid to a point of the tile

# ------------------------------------------------------------------ ball enumeration
def _balls_of_type(args):
    """the distinct accepted balls among the central level-m supertile of sigma^m(tau) for one type"""
    from scipy.spatial import cKDTree
    ti, G0, T0_, c, dec, R, m = args
    G, T = G0, T0_
    for _ in range(m): G, T = inflate(G, T, dec)
    P = Patch(G, T); X = centroid14(G, T); tree = cKDTree(X.astype(float))
    # completeness: the nearest cube centre that is NOT owned inside the patch (including a frame of virtual cubes just outside
    # the bounding box) must be at distance >= R + sqrt(3)/2 from x_t
    sh = np.array(P.shape); pad = -np.ones(tuple(sh + 2), dtype=np.int64); pad[1:-1, 1:-1, 1:-1] = P.grid
    bad = np.argwhere(pad < 0) - 1 + P.lo; btree = cKDTree((14 * bad + 7).astype(float))
    reach = 14 * (R + math.sqrt(3) / 2)
    ts = np.arange(c * 8 ** m, (c + 1) * 8 ** m); dmin, _ = btree.query(X[ts].astype(float))
    out = {}; rejected = int((dmin < reach).sum()); good = ts[dmin >= reach]
    R2_14 = 196 * R * R
    def chunks():                                      # query in chunks: all centres at once would hold ~1e8 indices at m = 5
        for s0 in range(0, len(good), 256):
            g = good[s0:s0 + 256]; yield from zip(g, tree.query_ball_point(X[g].astype(float), 14 * R + 1e-6))
    for t, cand in chunks():
        cand = np.array(cand); d2 = ((X[cand] - X[t]) ** 2).sum(1); mem = cand[d2 < R2_14]; Gt = G[t]
        Grel = np.einsum('ji,njk->nik', Gt, G[mem]); Trel = (T[mem] - T[t]) @ Gt
        rows = np.c_[Grel.reshape(len(mem), 9), Trel]; order = np.lexsort(rows.T[::-1])
        kb = rows[order].astype(np.int16).tobytes()
        if kb not in out: out[kb] = (Grel[order].astype(np.int8), Trel[order].astype(np.int16), (ti, int(t - c * 8 ** m)))
    return out, rejected, len(ts)

def enumerate_balls(dec, R, m, types_=None, nproc=1):
    """distinct legal R-balls: {canonical bytes: (G_rel, T_rel, (type index, tile index in the central supertile))} with poses
    relative to the centre tile (which has relative pose (I, 0)), plus counts"""
    if types_ is None: types_, _, _ = legal_types(dec)
    jobs = [(ti, G, T, c, dec, R, m) for ti, (G, T, c) in enumerate(types_.values())]
    balls = {}; rejected = 0; centres = 0
    if nproc > 1:
        import multiprocessing as mp
        with mp.Pool(nproc) as pool:
            for out, rej, n in pool.imap_unordered(_balls_of_type, jobs):
                rejected += rej; centres += n
                for kb, v in out.items(): balls.setdefault(kb, v)
    else:
        for j in jobs:
            out, rej, n = _balls_of_type(j); rejected += rej; centres += n
            for kb, v in out.items(): balls.setdefault(kb, v)
    return balls, {'types': len(types_), 'centres': centres, 'rejected': rejected, 'distinct': len(balls)}

def ball_amplified(G, T, rho, amp_of):
    """the amplified ball operator 24 - A~ (complex CSR) and the plain one; amp_of(d2_196) = 1/c(d/rho) as float"""
    G = G.astype(np.int64); T = T.astype(np.int64); P = Patch(G, T); a, b, k = P.panels(); U = link_matrices(G, a, b, k)
    X = centroid14(G, T); d2 = ((X[a] - X[b]) ** 2).sum(1)
    w = np.array([amp_of(int(v)) for v in d2])
    return hermitian(P.n, a, b, U, 24, scale=w), hermitian(P.n, a, b, U, 24), d2

def real_form_interleaved(H):
    """real symmetric form of a Hermitian CSR H, indices (2i, 2i+1) = (Re, Im) of complex index i"""
    Hr = H.real.tocoo(); Hi = H.imag.tocoo(); n = H.shape[0]
    rows = np.concatenate([2 * Hr.row, 2 * Hr.row + 1, 2 * Hi.row, 2 * Hi.row + 1]); cols = np.concatenate([2 * Hr.col, 2 * Hr.col + 1, 2 * Hi.col + 1, 2 * Hi.col])
    vals = np.concatenate([Hr.data, Hr.data, -Hi.data, Hi.data])
    A = sps.csr_matrix((vals, (rows, cols)), shape=(2 * n, 2 * n)); A.sum_duplicates(); A.eliminate_zeros(); return A

U_CERT = 2.0 ** -52          # two ulps of IEEE double: covers FMA and any summation order

def banded_cert(Hc, mu, entry_err=0.0):
    """rigorous lower bound on lambda_min(Hc) (Hc Hermitian CSR with exactly representable entries; mu a float such that the
    diagonal subtraction is exact), or None if the Cholesky of Hc - mu breaks down.  Returns (bound, bandwidth)"""
    from scipy.sparse.csgraph import reverse_cuthill_mckee
    A = real_form_interleaved(Hc); N = A.shape[0]
    p = reverse_cuthill_mckee(A, symmetric_mode=True); A = A[p][:, p].tocoo()
    low = A.row >= A.col; r, c, v = A.row[low], A.col[low], A.data[low]
    bw = int((r - c).max()); ab = np.zeros((bw + 1, N)); ab[r - c, c] = v; ab[0] -= float(mu)
    assert np.all(ab[0] + float(mu) == np.array(Hc.diagonal().real.repeat(2))[p])     # the diagonal subtraction was exact
    try:
        Lb = sl.cholesky_banded(ab, lower=True, overwrite_ab=True, check_finite=False)
    except np.linalg.LinAlgError:
        return None, bw
    if not (Lb[0] > 0).all(): return None, bw
    K = Lb.size; fro2 = float(np.sum(Lb * Lb)) * (1 + 2 * K * U_CERT)
    gam = (N + 1) * U_CERT / (1 - (N + 1) * U_CERT)
    return float(mu) - gam * fro2 * (1 + 2 * U_CERT) - entry_err, bw

def amp_table_exact(rho, d2_values):
    """the same, evaluating eta = sqrt(d2)/(14 rho) at 60 digits (rho a Fraction)"""
    import mpmath as mp
    mp.mp.dps = 60; tab = {}
    for v in sorted(d2_values):
        eta = mp.sqrt(mp.mpf(int(v))) / 14 / (mp.mpf(rho.numerator) / rho.denominator)
        assert 0 < eta < 1
        tab[int(v)] = float(1 / c_overlap(eta, dps=60))
    return tab

# ------------------------------------------------------------------ workers
_W = {}
def _cert_one(args):
    kb, G, T = args; rho, tab, mu, err = _W['rho'], _W['tab'], _W['mu'], _W['err']
    Ha, _, d2 = ball_amplified(G, T, rho, tab.__getitem__)
    low, bw = banded_cert(Ha, mu, err)
    return kb, low, bw, len(G)
def _init(rho, tab, mu, err):
    os.environ['OMP_NUM_THREADS'] = '1'; _W.update(rho=rho, tab=tab, mu=mu, err=err)

def certify(spec, R, m, nproc, mu_str, tag=None):
    import multiprocessing as mp
    dec = rule(spec); rho = Fraction(R) - RC_BOUND
    t0 = time.time(); types_, n0, _ = legal_types(dec); log(f"rule {spec}: {len(types_)} Phi-closed 1-star types ({n0} in T5) [{time.time()-t0:.0f}s]")
    fg = frame_graph(dec); log('frame substitution', fg)
    t0 = time.time(); balls, info = enumerate_balls(dec, R, m, types_, nproc); log(f"R={R} m={m}: {info} [{time.time()-t0:.0f}s]")
    assert info['rejected'] == 0, 'incomplete balls: increase m'
    # the squared centroid distances across panels: collect from the legal 1-stars (every panel is a centre-tile panel of a 1-star)
    d2s = set()
    for G, T, c in types_.values():
        P = Patch(G, T); a, b, _ = P.panels(); X = centroid14(G, T); d2s |= set(((X[a] - X[b]) ** 2).sum(1).tolist())
    tab = amp_table_exact(rho, d2s); amax = max(tab.values())
    err = 24 * amax * 2.0 ** -52                         # entrywise error of the rounded amplification factors (row-sum bound)
    mu = Fraction(math.floor(Fraction(mu_str) * 2 ** 20), 2 ** 20)
    items = [(kb, G, T) for kb, (G, T, _) in balls.items()]; res = []; fails = []
    t0 = time.time()
    with mp.Pool(nproc, initializer=_init, initargs=(float(rho), tab, float(mu), err)) as pool:
        for i, (kb, low, bw, nt) in enumerate(pool.imap_unordered(_cert_one, items, chunksize=8)):
            res.append((low, bw, nt))
            if low is None: fails.append(kb)
            if i % 1000 == 0: log(f"{i + 1}/{len(items)} certified, {len(fails)} failed [{time.time()-t0:.0f}s]")
    ok = not fails; lows = [r[0] for r in res if r[0] is not None]
    rec = {'rule': str(spec), 'R': R, 'm': m, 'rho': f'{rho.numerator}/{rho.denominator}', 'one_star_types': len(types_), 'one_star_types_T5': n0,
           'frame_graph': fg, 'centres': info['centres'], 'distinct_balls': info['distinct'], 'rejected_incomplete': info['rejected'],
           'ball_tiles': [min(r[2] for r in res), max(r[2] for r in res)], 'bandwidth_max': max(r[1] for r in res),
           'mu': f'{mu.numerator}/{mu.denominator}', 'mu_float': float(mu), 'amp_max': amax, 'entry_err': err,
           'Lambda_R_certified': min(lows) if ok else None, 'all_balls_certified': ok, 'balls_failing': len(fails),
           'implementation': 'phase11_chair (independent): own enumeration, RCM + banded LAPACK dpbtrf, Higham Thm 10.3 with u = 2^-52',
           'cert_seconds': time.time() - t0, 'tag': tag}
    log(rec)
    with open(os.path.join(RES, 'phase11_cert.jsonl'), 'a') as f: f.write(json.dumps(rec) + '\n')
    return rec

if __name__ == '__main__':
    if sys.argv[1] == 'cert':
        spec, R, m, nproc, mu = sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]), sys.argv[6]
        certify(spec, R, m, nproc, mu, sys.argv[7] if len(sys.argv) > 7 else None)

def probe(spec, R, m, tiles_per_type=24, seed=0, types_subset=None, nproc=4):
    """an UPPER bound on Lambda_R (and on D_R): the minimum of the amplified (and plain) ball bottoms over a sample of legal balls.
    Every sampled ball is legal and complete, so min over the sample >= Lambda_R; if it is below a target mu, no certificate at
    radius R can reach mu.  Float eigenvalues (scipy eigsh, residual-checked)."""
    import scipy.sparse.linalg as sla
    from scipy.spatial import cKDTree
    dec = rule(spec); rho = Fraction(R) - RC_BOUND; types_, _, _ = legal_types(dec); keys = list(types_)
    d2s = set()
    for G, T, c in types_.values():
        P = Patch(G, T); a, b, _ = P.panels(); X = centroid14(G, T); d2s |= set(((X[a] - X[b]) ** 2).sum(1).tolist())
    tab = amp_table_exact(rho, d2s); rng = np.random.default_rng(seed); out = []
    for ti in (types_subset if types_subset is not None else range(len(keys))):
        G, T, c = types_[keys[ti]]
        for _ in range(m): G, T = inflate(G, T, dec)
        X = centroid14(G, T); tree = cKDTree(X.astype(float)); P = Patch(G, T)
        sh = np.array(P.shape); pad = -np.ones(tuple(sh + 2), dtype=np.int64); pad[1:-1, 1:-1, 1:-1] = P.grid
        bad = np.argwhere(pad < 0) - 1 + P.lo; btree = cKDTree((14 * bad + 7).astype(float))
        ts = np.arange(c * 8 ** m, (c + 1) * 8 ** m); dmin, _ = btree.query(X[ts].astype(float)); ok = ts[dmin >= 14 * (R + math.sqrt(3) / 2)]
        for t in rng.choice(ok, min(tiles_per_type, len(ok)), replace=False):
            mem = np.array(tree.query_ball_point(X[t].astype(float), 14 * R + 1e-6)); mem = mem[((X[mem] - X[t]) ** 2).sum(1) < 196 * R * R]
            Ha, Hp, _ = ball_amplified(G[mem], T[mem], rho, tab.__getitem__)
            la, va = sla.eigsh(Ha, k=1, which='SA', tol=1e-12, ncv=60); lp = sla.eigsh(Hp, k=1, which='SA', tol=1e-12, ncv=60, return_eigenvectors=False)[0]
            res = float(np.linalg.norm(Ha @ va[:, 0] - la[0] * va[:, 0]))
            out.append({'type': int(ti), 'tile': int(t), 'tiles': int(len(mem)), 'Lambda_ball': float(la[0]), 'residual': res, 'D_ball': float(lp)})
    out.sort(key=lambda r: r['Lambda_ball'])
    return {'rule': str(spec), 'R': R, 'm': m, 'sampled_balls': len(out), 'Lambda_R_upper_float': out[0]['Lambda_ball'] + out[0]['residual'],
            'D_R_upper_float': min(r['D_ball'] for r in out), 'lowest': out[:5]}

def _probe_ball(args):
    G, T, rho, tab = args
    import scipy.sparse.linalg as sla
    Ha, Hp, _ = ball_amplified(G, T, rho, tab.__getitem__)
    la, va = sla.eigsh(Ha, k=1, which='SA', tol=1e-11, ncv=60); lp = sla.eigsh(Hp, k=1, which='SA', tol=1e-11, ncv=60, return_eigenvectors=False)[0]
    v = va[:, 0]; rq = float(np.real(np.vdot(v, Ha @ v)) / np.real(np.vdot(v, v)))       # Rayleigh quotient: >= Lambda of this ball
    return {'tiles': int(len(G)), 'Lambda_ball_rayleigh': rq, 'D_ball': float(lp)}

def probe_parallel(spec, Rs, m, type_indices, tiles_per_type, nproc=4, seed=0):
    """upper bounds on Lambda_R and D_R from sampled legal balls (types chosen by the caller), parallel over balls"""
    import multiprocessing as mp
    from scipy.spatial import cKDTree
    dec = rule(spec); types_, _, _ = legal_types(dec); keys = list(types_); rng = np.random.default_rng(seed); out = []
    d2s = set()
    for G, T, c in types_.values():
        P = Patch(G, T); a, b, _ = P.panels(); X = centroid14(G, T); d2s |= set(((X[a] - X[b]) ** 2).sum(1).tolist())
    inflated = {}
    for ti in type_indices:
        G, T, c = types_[keys[ti]]
        for _ in range(m): G, T = inflate(G, T, dec)
        inflated[ti] = (G, T, c)
    for R in Rs:
        rho = Fraction(R) - RC_BOUND; tab = amp_table_exact(rho, d2s); jobs = []
        for ti, (G, T, c) in inflated.items():
            X = centroid14(G, T); tree = cKDTree(X.astype(float)); P = Patch(G, T)
            sh = np.array(P.shape); pad = -np.ones(tuple(sh + 2), dtype=np.int64); pad[1:-1, 1:-1, 1:-1] = P.grid
            bad = np.argwhere(pad < 0) - 1 + P.lo; btree = cKDTree((14 * bad + 7).astype(float))
            ts = np.arange(c * 8 ** m, (c + 1) * 8 ** m); dmin, _ = btree.query(X[ts].astype(float)); ok = ts[dmin >= 14 * (R + math.sqrt(3) / 2)]
            for t in rng.choice(ok, min(tiles_per_type, len(ok)), replace=False):
                mem = np.array(tree.query_ball_point(X[t].astype(float), 14 * R + 1e-6)); mem = mem[((X[mem] - X[t]) ** 2).sum(1) < 196 * R * R]
                jobs.append((G[mem], T[mem], float(rho), tab))
        with mp.Pool(nproc) as pool: res = pool.map(_probe_ball, jobs, chunksize=1)
        rec = {'rule': str(spec), 'R': R, 'm': m, 'types': list(type_indices), 'sampled_balls': len(res),
               'Lambda_R_upper': min(r['Lambda_ball_rayleigh'] for r in res), 'D_R_upper_float': min(r['D_ball'] for r in res),
               'ball_tiles': [min(r['tiles'] for r in res), max(r['tiles'] for r in res)]}
        print(rec, flush=True); out.append(rec)
    return out
