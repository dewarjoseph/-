#!/usr/bin/env python3
"""Phase XII, Parts I and IX: a second independent implementation of the Chair44 objects.

Written from deliverables/PHASE7_DEFINITIONS.md alone; it imports no phase5-11 module.  Deliberately different from
phase11_chair at every step that a shared bug could hide in:
  frames        integer indices into the 48 signed permutation matrices, with exact product/transpose tables
  links         quaternions: sigma_k = i q_k, so (sigma . u_a)(sigma . u_b) = -s_a s_b q_{k_a} q_{k_b} in Q8 (derived, not tabulated)
  operator      the spinor representation realified: the real 4x4 left-multiplication matrices L(q) of the quaternions
                (C^2 with Q8 acting is H with left multiplication); H = 24 - A has the spinor spectrum, each eigenvalue doubled
  keys          a legal ball is the sorted list of (relative frame index, G_t^T (T_a - T_t)); 4 int16 columns
  completeness  every cube centre within R + sqrt(3)/2 of the centre's centroid is owned (checked against a KD-tree of the
                unowned cube centres of a one-cube padding of the patch)
  certificate   real symmetric 4n x 4n banded Cholesky (scipy) after reverse Cuthill-McKee, Higham Thm 10.3 bound
                lambda_min >= mu - gamma_{n+1} ||L||_F^2 (1 + 2Ku) - entry error, u = 2^-52
Commands (results go to audit/results/phase12_independent.jsonl):
  types <rule>                         number of Phi-closed legal 1-star types
  Y <rule> <L>                         exact rational upper bound Y_L (pinned level-L supertile)
  cert <rule> <R> <m> <nproc> <mu> <tag>   streaming legal-ball enumeration and IMS certificate at radius R
Rule specs: census index (proper, base-3 digits) or x<extended index> (base-6 digits), as in Phases IX-XI."""
import os, sys, json, math, time, zlib, itertools, collections
from fractions import Fraction
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__)); RES = os.path.join(HERE, 'results')
OUT = os.path.join(RES, 'phase12_independent.jsonl')
T0 = time.time()
def log(*a): print(f"[{time.time() - T0:8.0f}s]", *a, flush=True)

# ---------------------------------------------------------------- frames
PERM3 = list(itertools.permutations(range(3)))
def pmat(p):
    M = np.zeros((3, 3), dtype=np.int64)
    for i in range(3): M[i, p[i]] = 1
    return M
FRAMES = [np.diag(s) @ pmat(p) for p in PERM3 for s in itertools.product((1, -1), repeat=3)]   # 48 signed permutations
FKEY = {tuple(F.ravel()): i for i, F in enumerate(FRAMES)}
def fidx(M): return FKEY[tuple(np.asarray(M).ravel())]
FMUL = np.array([[fidx(A @ B) for B in FRAMES] for A in FRAMES], dtype=np.int64)
FTR = np.array([fidx(A.T) for A in FRAMES], dtype=np.int64)
REL = FMUL[FTR]                                    # REL[i, j] = index of F_i^T F_j
FARR = np.array(FRAMES)
OCTANTS = [v for v in itertools.product((0, 1), repeat=3) if v != (1, 1, 1)]
EVEN = [p for p in PERM3 if round(np.linalg.det(pmat(p))) == 1]; ODD = [p for p in PERM3 if round(np.linalg.det(pmat(p))) == -1]

def decoration(spec):
    """(centre permutation, 7 octant permutations) from a census index or x<extended index>"""
    spec = str(spec)
    if spec.startswith('x'):
        j = int(spec[1:]); return [PERM3[(j // 6 ** c) % 6] for c in range(8)]
    i = int(spec); dg = [(i // 3 ** k) % 3 for k in range(8)]
    return [EVEN[dg[0]]] + [(EVEN if sum(v) % 2 == 0 else ODD)[dg[k + 1]] for k, v in enumerate(OCTANTS)]
def children_ops(dec):
    """frame factor indices and translations of the 8 children: child of (G, T) is (G h, 2T + G t)"""
    h = [fidx(pmat(dec[0]))] + [fidx(np.diag([1 - 2 * x for x in v]) @ pmat(dec[k + 1])) for k, v in enumerate(OCTANTS)]
    t = [np.array([1, 1, 1])] + [4 * np.array(v) for v in OCTANTS]
    return np.array(h), np.array(t, dtype=np.int64)
def inflate(f, T, dec):
    """tiles (frame index f, position T) -> their 8 children each, child c of tile n at row 8n + c"""
    h, t = children_ops(dec)
    fc = FMUL[f[:, None], h[None, :]].reshape(-1)
    Tc = (2 * T[:, None, :] + np.einsum('nij,cj->nci', FARR[f], t)).reshape(-1, 3)
    return fc, Tc

# ---------------------------------------------------------------- geometry
BASE = np.array([[2 * a + 1, 2 * b + 1, 2 * c + 1] for a, b, c in OCTANTS], dtype=np.int64)
def cubes(f, T): return (np.einsum('nij,uj->nui', FARR[f], BASE) + 2 * T[:, None, :] - 1) // 2
def centroid14(f, T): return 14 * T + 13 * FARR[f].sum(-1)
class Owner:
    """owner map of a finite set of tiles on a padded grid (one empty cube layer around the bounding box)"""
    def __init__(self, f, T):
        Q = cubes(f, T).reshape(-1, 3); self.lo = Q.min(0) - 1; Q = Q - self.lo; self.shape = tuple(Q.max(0) + 2)
        self.grid = np.full(self.shape, -1, dtype=np.int64); idx = tuple(Q.T)
        assert (self.grid[idx] == -1).all(); self.grid[idx] = np.repeat(np.arange(len(f)), 7)
        assert np.count_nonzero(self.grid >= 0) == 7 * len(f), 'tiles overlap'
    def panels(self):
        out = []
        for k in range(3):
            a = np.moveaxis(self.grid, k, 0)[:-1].ravel(); b = np.moveaxis(self.grid, k, 0)[1:].ravel()
            m = (a >= 0) & (b >= 0) & (a != b); out.append(np.stack([a[m], b[m], np.full(m.sum(), k)], 1))
        return np.concatenate(out)
    def owner(self, q):
        q = q - self.lo; ok = ((q >= 0) & (q < np.array(self.shape))).all(-1); r = np.full(q.shape[:-1], -1, dtype=np.int64)
        r[ok] = self.grid[tuple(q[ok].T)]; return r

# ---------------------------------------------------------------- links as quaternions
# quaternion basis (1, i, j, k) = (1, q1, q2, q3); q_k = -i sigma_k (PHASE7_DEFINITIONS section 3)
def qmul(a, b):
    a0, a1, a2, a3 = a; b0, b1, b2, b3 = b
    return (a0 * b0 - a1 * b1 - a2 * b2 - a3 * b3, a0 * b1 + a1 * b0 + a2 * b3 - a3 * b2,
            a0 * b2 - a1 * b3 + a2 * b0 + a3 * b1, a0 * b3 + a1 * b2 - a2 * b1 + a3 * b0)
UNIT = [(0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)]
def link_quaternion(row_a, row_b):
    """(sigma . u_a)(sigma . u_b) for signed basis vectors u = M^T e_k (row k of M): sigma_k = i q_k, so the product is
    (i)^2 s_a s_b q_{k_a} q_{k_b} = -s_a s_b q_{k_a} q_{k_b}"""
    ka = int(np.flatnonzero(row_a)[0]); kb = int(np.flatnonzero(row_b)[0]); s = int(row_a[ka] * row_b[kb])
    return tuple(-s * x for x in qmul(UNIT[ka], UNIT[kb]))
def Lmat(q):
    """real 4x4 matrix of left multiplication by q on H = R^4"""
    return np.array([qmul(q, e) for e in ((1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1))], dtype=np.int64).T
Q8 = [(1, 0, 0, 0), (-1, 0, 0, 0), (0, 1, 0, 0), (0, -1, 0, 0), (0, 0, 1, 0), (0, 0, -1, 0), (0, 0, 0, 1), (0, 0, 0, -1)]
QIDX = {q: i for i, q in enumerate(Q8)}
LINK = np.array([[[QIDX[link_quaternion(FRAMES[i][k], FRAMES[j][k])] for k in range(3)] for j in range(48)] for i in range(48)])
_LQ = [Lmat(q) for q in Q8]                       # each L(q) is a signed 4x4 permutation matrix: 4 nonzeros
NZR = np.array([np.nonzero(L)[0] for L in _LQ]); NZC = np.array([np.nonzero(L)[1] for L in _LQ])
NZV = np.array([L[np.nonzero(L)] for L in _LQ])
def operator(f, T, weight=None, diag=24.0):
    """real symmetric 4n x 4n matrix of diag - A, A the realified spinor adjacency: the block of panel (a, b, k) is L(U(a->b)),
    its transpose L(U(b->a)) = L(U(a->b))^T; weight(d2_196) (a function on arrays) scales each panel"""
    import scipy.sparse as sps
    O = Owner(f, T); P = O.panels(); n = len(f); a, b, k = P[:, 0], P[:, 1], P[:, 2]
    li = LINK[f[a], f[b], k]; X = centroid14(f, T)
    w = np.ones(len(P)) if weight is None else weight(((X[a] - X[b]) ** 2).sum(1))
    r = 4 * a[:, None] + NZR[li]; c = 4 * b[:, None] + NZC[li]; v = -w[:, None] * NZV[li]
    H = sps.csr_matrix((np.r_[v.ravel(), v.ravel()], (np.r_[r.ravel(), c.ravel()], np.r_[c.ravel(), r.ravel()])), shape=(4 * n, 4 * n))
    H.sum_duplicates()
    return (H + diag * sps.eye(4 * n, format='csr')).tocsr()
def weight_fn(tab):
    keys = np.array(sorted(tab)); vals = np.array([tab[k] for k in keys])
    def w(d2):
        i = np.searchsorted(keys, d2); assert np.array_equal(keys[i], d2), 'unknown panel distance'; return vals[i]
    return w

# ---------------------------------------------------------------- exact supertile upper bounds
def supertile(dec, L):
    f = np.array([fidx(np.eye(3, dtype=np.int64))]); T = np.zeros((1, 3), dtype=np.int64)
    for _ in range(L): f, T = inflate(f, T, dec)
    return f, T
def exact_rayleigh(H, v, scale=2 ** 20):
    """exact rational Rayleigh quotient of the integer rounding of v (H with integer entries)"""
    x = np.rint(v / np.abs(v).max() * scale).astype(np.int64); Hi = H.astype(np.int64)
    assert np.array_equal(Hi.data, H.data)
    y = Hi @ x; return Fraction(int(np.dot(x.astype(object), y.astype(object))), int(np.dot(x.astype(object), x.astype(object))))
def Y(spec, L):
    import scipy.sparse.linalg as sla
    f, T = supertile(decoration(spec), L); H = operator(f, T)
    if H.shape[0] <= 3000: w, V = np.linalg.eigh(H.toarray()); lam, v = w[0], V[:, 0]
    else: w, V = sla.eigsh(H, k=1, which='SA', tol=1e-11, ncv=40); lam, v = w[0], V[:, 0]
    return float(lam), exact_rayleigh(H, v)

# ---------------------------------------------------------------- legal 1-star types and the Phi-closure
CHEB1 = np.array([o for o in itertools.product(range(-1, 2), repeat=3) if o != (0, 0, 0)])
def star_tiles(O, f, T, t):
    """tiles owning a cube at Chebyshev distance <= 1 from a cube of t; None if some such cube is unowned"""
    q = cubes(f[t:t + 1], T[t:t + 1])[0]; nb = (q[:, None, :] + CHEB1[None]).reshape(-1, 3)
    own = O.owner(np.unique(np.vstack([q, nb]), axis=0))
    return None if (own < 0).any() else sorted(set(own.tolist()))
def star_key(f, T, mem, t):
    return tuple(sorted((int(REL[f[t], f[b]]), *map(int, FARR[f[t]].T @ (T[b] - T[t]))) for b in mem))
def legal_types(dec, L0=5):
    f, T = supertile(dec, L0); O = Owner(f, T); types = {}
    for t in range(len(f)):
        mem = star_tiles(O, f, T, t)
        if mem is None: continue
        k = star_key(f, T, mem, t)
        if k not in types: types[k] = (f[mem], T[mem], mem.index(t))
    n0 = len(types); queue = list(types)
    while queue:
        fs, Ts, c = types[queue.pop()]
        fi, Ti = inflate(fs, Ts, dec); O = Owner(fi, Ti)
        for t in range(8 * c, 8 * c + 8):
            mem = star_tiles(O, fi, Ti, t); assert mem is not None, 'closure lemma fails'
            k = star_key(fi, Ti, mem, t)
            if k not in types: types[k] = (fi[mem], Ti[mem], mem.index(t)); queue.append(k)
    return types, n0

# ---------------------------------------------------------------- the overlap function and amplification
def overlap(eta, dps=50):
    import mpmath as mp
    mp.mp.dps = dps; e = mp.mpf(eta); pi = mp.pi
    return (pi * (1 - e / 2) * mp.sin(pi * e) + 1 - mp.cos(pi * e)) / (pi ** 2 * e)
RC = Fraction(311, 175)
def amp_table(rho, d2_values):
    import mpmath as mp
    mp.mp.dps = 50; out = {}
    for d2 in d2_values:
        eta = mp.sqrt(mp.mpf(d2)) / 14 / (mp.mpf(rho.numerator) / rho.denominator); assert 0 < eta < 1
        out[d2] = float(1 / overlap(eta))
    return out

# ---------------------------------------------------------------- legal balls (streaming) and the certificate
def _patch(args):
    from scipy.spatial import cKDTree
    fs, Ts, c, dec, R, m = args
    f, T = fs, Ts
    for _ in range(m): f, T = inflate(f, T, dec)
    O = Owner(f, T); X = centroid14(f, T); tree = cKDTree(X.astype(float))
    empty = np.argwhere(O.grid < 0) + O.lo; etree = cKDTree((14 * empty + 7).astype(float))
    cen = np.arange(c * 8 ** m, (c + 1) * 8 ** m)
    dist, _ = etree.query(X[cen].astype(float)); ok = dist >= 14 * (R + math.sqrt(3) / 2)
    return f, T, X, tree, cen, ok
def _ball(f, T, X, cand, t, R):
    cand = np.asarray(cand); d2 = ((X[cand] - X[t]) ** 2).sum(1); mem = cand[d2 < 196 * R * R]
    rows = np.empty((len(mem), 4), dtype=np.int64); rows[:, 0] = REL[f[t], f[mem]]; rows[:, 1:] = (T[mem] - T[t]) @ FARR[f[t]]
    o = np.lexsort(rows.T[::-1]); return rows[o].astype(np.int16).tobytes(), mem[o]
def _keys(args):
    ti = args[0]; f, T, X, tree, cen, ok = _patch(args[1:]); R = args[5]; raw = {}
    good = cen[ok]
    for s in range(0, len(good), 256):
        g = good[s:s + 256]
        for t, cand in zip(g, tree.query_ball_point(X[g].astype(float), 14 * R + 1e-6)):
            kb, _ = _ball(f, T, X, cand, t, R); raw.setdefault(kb, int(t))
    return ti, {zlib.compress(k, 1): t for k, t in raw.items()}, int((~ok).sum()), len(cen)
_W = {}
def _init(tab, mu, err): _W.update(tab=tab, mu=mu, err=err)
def higham(Hs, mu, err):
    """rigorous lower bound on lambda_min of the real symmetric sparse Hs (exact entries up to err in row sum), or None"""
    import scipy.linalg as sl
    from scipy.sparse.csgraph import reverse_cuthill_mckee
    N = Hs.shape[0]; p = reverse_cuthill_mckee(Hs.tocsr(), symmetric_mode=True); A = Hs[p][:, p].tocoo()
    lo = A.row >= A.col; r, c, v = A.row[lo], A.col[lo], A.data[lo]; bw = int((r - c).max())
    ab = np.zeros((bw + 1, N)); ab[r - c, c] = v; d0 = ab[0].copy(); ab[0] = d0 - mu
    assert np.array_equal(ab[0] + mu, d0), 'shift not exact'
    try: Lb = sl.cholesky_banded(ab, lower=True, overwrite_ab=True, check_finite=False)
    except np.linalg.LinAlgError: return None, bw
    if not (Lb[0] > 0).all(): return None, bw
    u = 2.0 ** -52; K = Lb.size; fro2 = float(np.sum(Lb * Lb)) * (1 + 2 * K * u); gam = (N + 1) * u / (1 - (N + 1) * u)
    return mu - gam * fro2 * (1 + 2 * u) - err, bw
def _cert(args):
    ti, fs, Ts, c, dec, R, m, ts, zks = args; tab, mu, err = _W['tab'], _W['mu'], _W['err']
    f, T, X, tree, cen, ok = _patch((fs, Ts, c, dec, R, m)); out = []
    for t, cand, zk in zip(ts, tree.query_ball_point(X[np.array(ts)].astype(float), 14 * R + 1e-6), zks):
        kb, mem = _ball(f, T, X, cand, t, R); assert zlib.compress(kb, 1) == zk
        H = operator(f[mem], T[mem], weight=weight_fn(tab))
        low, bw = higham(H, mu, err)
        if low is None:
            import scipy.sparse.linalg as sla
            out.append((None, bw, len(mem), float(sla.eigsh(H, k=1, which='SA', tol=1e-10, return_eigenvectors=False)[0]), int(t)))
        else: out.append((low, bw, len(mem)))
    return ti, out
def certify(spec, R, m, nproc, mu_str, tag):
    import multiprocessing as mp
    dec = decoration(spec); rho = Fraction(R) - RC
    t0 = time.time(); types, n0 = legal_types(dec); tv = list(types.values()); log(f'{spec}: {len(types)} legal 1-star types ({n0} in T5)')
    jobs = [(ti, fs, Ts, c, dec, R, m) for ti, (fs, Ts, c) in enumerate(tv)]; seen = {}; rej = 0; centres = 0
    with mp.Pool(nproc) as pool:
        for ti, ks, r_, n_ in pool.imap(_keys, jobs):
            rej += r_; centres += n_
            for zk, t in ks.items(): seen.setdefault(zk, (ti, t))
            if ti % 10 == 0: log(f'  pass 1: type {ti + 1}/{len(jobs)}, {len(seen)} distinct')
    log(f'R={R} m={m}: {len(seen)} distinct balls, {centres} centres, {rej} rejected [{time.time() - t0:.0f}s]')
    assert rej == 0, 'incomplete balls: increase m'
    d2s = set()
    for fs, Ts, c in tv:
        P = Owner(fs, Ts).panels(); X = centroid14(fs, Ts); d2s |= {int(((X[a] - X[b]) ** 2).sum()) for a, b, _ in P}
    tab = amp_table(rho, sorted(d2s)); err = 24 * max(tab.values()) * 2.0 ** -52
    mu = float(Fraction(math.floor(Fraction(mu_str) * 2 ** 20), 2 ** 20))
    own = collections.defaultdict(list)
    for zk, (ti, t) in seen.items(): own[ti].append((t, zk))
    cj = []
    for ti, lst in sorted(own.items()):
        lst.sort(); fs, Ts, c = tv[ti]
        for s in range(0, len(lst), 128): cj.append((ti, fs, Ts, c, dec, R, m, [a for a, _ in lst[s:s + 128]], [b for _, b in lst[s:s + 128]]))
    nb = len(seen); del seen; res = []; fails = []; t1 = time.time()
    with mp.Pool(nproc, initializer=_init, initargs=(tab, mu, err)) as pool:
        for ti, out in pool.imap_unordered(_cert, cj):
            for o in out:
                res.append(o[:3])
                if o[0] is None: fails.append({'type': ti, 'tile': o[4], 'tiles': o[2], 'lambda_float': o[3]})
            log(f'  pass 2: {len(res)}/{nb} certified, {len(fails)} failed [{time.time() - t1:.0f}s]')
    ok = not fails; lows = [r[0] for r in res if r[0] is not None]
    rec = {'rule': str(spec), 'R': R, 'm': m, 'rho': str(rho), 'one_star_types': len(types), 'one_star_types_T5': n0, 'centres': centres,
           'distinct_balls': nb, 'rejected_incomplete': rej, 'ball_tiles': [min(r[2] for r in res), max(r[2] for r in res)],
           'bandwidth_max': max(r[1] for r in res), 'mu': f'{Fraction(mu).numerator}/{Fraction(mu).denominator}', 'entry_err': err,
           'Lambda_R_certified': min(lows) if ok else None, 'all_balls_certified': ok, 'balls_failing': len(fails),
           'failing_balls_lowest': sorted(fails, key=lambda x: x['lambda_float'])[:50], 'tag': tag, 'seconds': time.time() - t0,
           'implementation': 'phase12_independent: frame-index tables, quaternion links, realified spinor operator, own enumeration'}
    log({k: v for k, v in rec.items() if k != 'failing_balls_lowest'})
    with open(OUT, 'a') as fh: fh.write(json.dumps(rec) + '\n')
    return rec

if __name__ == '__main__':
    os.environ.setdefault('OMP_NUM_THREADS', '1')
    cmd = sys.argv[1]
    if cmd == 'types':
        types, n0 = legal_types(decoration(sys.argv[2])); print(len(types), n0)
    elif cmd == 'Y':
        lam, q = Y(sys.argv[2], int(sys.argv[3])); rec = {'rule': sys.argv[2], 'L': int(sys.argv[3]), 'float': lam, 'upper_num': str(q.numerator), 'upper_den': str(q.denominator), 'upper': float(q)}
        print(rec)
        with open(OUT, 'a') as fh: fh.write(json.dumps({'kind': 'Y', **rec}) + '\n')
    elif cmd == 'cert':
        certify(sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]), sys.argv[6], sys.argv[7])
