#!/usr/bin/env python3
"""Phase XII, Part VII: a second substitution family with a different geometry and a non-Q8 connection family.

Geometry (Cube48): tiles are unit cubes of Z^3 with a frame F (any of the 48 signed permutation matrices: the cube is symmetric
under all of them).  A decoration d = (h_v) assigns a frame factor h_v (48 choices) to each octant v in {0,1}^3; the child of
(F, centre x) at octant v is (F h_v, 2x + F(2v - 1)/2).  The geometry is decoration-independent (the level-L supertile is the
2^L block); only frames differ.  Degree 6 (the Chair44 complex has degree 24 and 7-cube tiles).
Connection family (theta): for the panel between cubes a (lower) and b (upper) along axis k, u = row k of the frame and
  U_theta(a -> b) = R_{u_a}(theta) R_{u_b}(theta)^{-1},  R_u(theta) = cos(theta) - i sin(theta) sigma.u,  U(b -> a) = U(a -> b)^{-1}.
At theta = pi/2 this is the Pauli link (sigma.u_a)(sigma.u_b) in Q8; for generic theta the holonomies leave every finite group.
Representations: spinor (2x2), adjoint (the SO(3) image, 3x3 real), and at theta = pi/2 the three shadows chi_k (1x1).
Operator: H = 6 - A on a tiling (pinned on finite patches).  E_* := inf sigma(H) on the hull.
Commands -> audit/results/phase12_cube.json (merged by key):
  orbit <seed> <n_rules> <L>     search n random rules for a high Y3 (theta = pi/2), then compare the right orbit d.Q of the best
                                 rule (48 Q) at levels 1..L in all representations, for theta = pi/2 and theta = pi/5
  cert <rule_key> <theta_num/den> <R> <m> <mu>   legal-ball IMS certificate (Higham) for one rule at theta = pi * num/den
  theta <rule_key> <L>           Y_L(theta), free F_L(theta) for theta = pi/2 ... pi/32 (small-theta scaling)
  flat                           the identity rule: flat connection, E_* = 0 (and why every Chair44 rule is not)"""
import os, sys, json, math, time, itertools, zlib
from fractions import Fraction
import numpy as np, scipy.sparse as sps, scipy.sparse.linalg as sla
HERE = os.path.dirname(os.path.abspath(__file__)); RES = os.path.join(HERE, 'results'); OUT = os.path.join(RES, 'phase12_cube.json')
T0 = time.time()
def log(*a): print(f"[{time.time() - T0:7.0f}s]", *a, flush=True)
def save(key, obj):
    d = json.load(open(OUT)) if os.path.exists(OUT) else {}
    d[key] = obj; json.dump(d, open(OUT, 'w'), indent=1, default=float)

PERM3 = list(itertools.permutations(range(3)))
def pmat(p):
    M = np.zeros((3, 3), dtype=np.int64)
    for i in range(3): M[i, p[i]] = 1
    return M
FR = [np.diag(s) @ pmat(p) for p in PERM3 for s in itertools.product((1, -1), repeat=3)]
FK = {tuple(F.ravel()): i for i, F in enumerate(FR)}
def fid(M): return FK[tuple(np.asarray(M).ravel())]
MUL = np.array([[fid(A @ B) for B in FR] for A in FR]); TR = np.array([fid(A.T) for A in FR]); REL = MUL[TR]
FA = np.array(FR); DET = np.array([round(np.linalg.det(F)) for F in FR])
OCT = list(itertools.product((0, 1), repeat=3)); SV = np.array([[2 * a - 1, 2 * b - 1, 2 * c - 1] for a, b, c in OCT])
SIG = np.array([[[0, 1], [1, 0]], [[0, -1j], [1j, 0]], [[1, 0], [0, -1]]])

def inflate(f, X2, dec):
    """children: frame f h_v, doubled centre 2 X2 + F (2v - 1) (X2 = 2 x, odd integers)"""
    fc = MUL[f[:, None], np.array(dec)[None, :]].reshape(-1)
    Xc = (2 * X2[:, None, :] + np.einsum('nij,vj->nvi', FA[f], SV)).reshape(-1, 3)
    return fc, Xc
def supertile(dec, L):
    f = np.array([fid(np.eye(3, dtype=np.int64))]); X2 = np.ones((1, 3), dtype=np.int64)
    for _ in range(L): f, X2 = inflate(f, X2, dec)
    return f, X2
def panels(X2):
    """(a, b, k), a the lower cube, b the upper along axis k"""
    q = (X2 - 1) // 2; key = {tuple(v): i for i, v in enumerate(q.tolist())}; A, B, K = [], [], []
    for i, v in enumerate(q.tolist()):
        for k in range(3):
            w = list(v); w[k] += 1; j = key.get(tuple(w))
            if j is not None: A.append(i); B.append(j); K.append(k)
    return np.array(A, dtype=np.int64), np.array(B, dtype=np.int64), np.array(K, dtype=np.int64)

def Rot(u, theta):
    return math.cos(theta) * np.eye(2) - 1j * math.sin(theta) * np.tensordot(u, SIG, 1)
def spinor_links(f, a, b, k, theta):
    """U_theta(a -> b); at theta = pi/2 exactly the Pauli link (sigma.u_a)(sigma.u_b), entries in {0, +-1, +-i}"""
    exact = abs(theta - math.pi / 2) < 1e-15; cache = {}; out = np.empty((len(a), 2, 2), dtype=complex)
    for e, (i, j, kk) in enumerate(zip(f[a], f[b], k)):
        key = (int(i), int(j), int(kk))
        if key not in cache:
            ua, ub = FA[i][kk], FA[j][kk]
            cache[key] = (np.tensordot(ua, SIG, 1) @ np.tensordot(ub, SIG, 1)) if exact else Rot(ua, theta) @ np.linalg.inv(Rot(ub, theta))
        out[e] = cache[key]
    return out
def adjoint(U):
    """SO(3) image: Ad(U)_{ij} = (1/2) tr(sigma_i U sigma_j U^+)"""
    return np.real(np.einsum('iab,nbc,jcd,nad->nij', SIG, U, SIG, np.conj(U)) / 2)
def shadow(U, m):
    """chi_m on Q8 links (theta = pi/2): +1 on +-1 and +-q_m, -1 on the other +-q_l"""
    out = np.empty(len(U))
    for e, u in enumerate(U):
        if abs(abs(u[0, 0]) - 1) < 1e-9 and abs(u[0, 1]) < 1e-9 and abs(u[0, 0] - u[1, 1]) < 1e-9: out[e] = 1.0; continue
        l = int(np.argmax([abs(np.trace(u @ SIG[i])) for i in range(3)])); out[e] = 1.0 if l == m else -1.0
    return out
def operator(n, a, b, blocks, diag=6.0, w=None):
    """diag - A, the block of panel (a, b) being U(a -> b) and of (b, a) its adjoint; diag a number or a per-tile array;
    w scales panels.  Complex CSR of size r n"""
    r = blocks.shape[1]
    if w is not None: blocks = blocks * w[:, None, None]
    ii, jj = np.meshgrid(np.arange(r), np.arange(r), indexing='ij')
    rows = np.concatenate([(r * a[:, None, None] + ii).ravel(), (r * b[:, None, None] + ii).ravel()])
    cols = np.concatenate([(r * b[:, None, None] + jj).ravel(), (r * a[:, None, None] + jj).ravel()])
    vals = np.concatenate([blocks.ravel(), np.conj(np.transpose(blocks, (0, 2, 1))).ravel()])
    A = sps.csr_matrix((-vals, (rows, cols)), shape=(r * n, r * n)); A.sum_duplicates()
    return (A + sps.diags(np.repeat(np.broadcast_to(np.asarray(diag, dtype=float), (n,)), r))).tocsr()
def bottom(H):
    if H.shape[0] <= 2500: return float(np.linalg.eigvalsh(H.toarray())[0])
    return float(sla.eigsh(H, k=1, which='SA', tol=1e-10, return_eigenvectors=False)[0])
def level_bottoms(dec, L, theta, free=False):
    """pinned (or free) bottoms of T_L in every representation"""
    f, X2 = supertile(dec, L); a, b, k = panels(X2); n = len(f); U = spinor_links(f, a, b, k, theta)
    diag = 6.0 if not free else (np.bincount(a, minlength=n) + np.bincount(b, minlength=n)).astype(float)
    def op(bl): return operator(n, a, b, bl, diag=diag)
    out = {'spinor': bottom(op(U)), 'adjoint': bottom(op(adjoint(U).astype(complex)))}
    if abs(theta - math.pi / 2) < 1e-12:
        for m in range(3): out['chi%d' % (m + 1)] = bottom(op(shadow(U, m)[:, None, None].astype(complex)))
    return out

def right(dec, q): return [int(MUL[h, q]) for h in dec]
def rule_key(dec): return '.'.join(map(str, dec))
def parse_key(s): return [int(x) for x in s.split('.')]

def cmd_orbit(seed, n_rules, L):
    rng = np.random.default_rng(seed); best = None; t0 = time.time()
    for _ in range(n_rules):
        dec = [int(x) for x in rng.integers(0, 48, 8)]
        y = level_bottoms(dec, 3, math.pi / 2)['spinor']
        if best is None or y > best[0]: best = (y, dec)
    log('best random rule', best, f'{time.time() - t0:.0f}s')
    dec = best[1]; rows = []
    for q in range(48):
        dq = right(dec, q); row = {'Q': q, 'det': int(DET[q]), 'rule': rule_key(dq)}
        for th_name, th in (('pi/2', math.pi / 2), ('pi/5', math.pi / 5)):
            for l in range(1, L + 1): row[f'{th_name}:L{l}'] = level_bottoms(dq, l, th)
        rows.append(row); log(q, {k: (v['spinor'] if isinstance(v, dict) else v) for k, v in row.items() if ':' in k})
    # level-1 isospectrality: proper Q for both theta; improper Q at theta = pi/2 only (the conjugation sign theta -> -theta)
    dev = {}
    for th in ('pi/2', 'pi/5'):
        for par in (1, -1):
            v = [r[f'{th}:L1']['spinor'] for r in rows if r['det'] == par]; dev[f'{th}:det{par:+d}:L1_spread'] = float(max(v) - min(v))
            for l in range(2, L + 1):
                v = [r[f'{th}:L{l}']['spinor'] for r in rows if r['det'] == par]; dev[f'{th}:det{par:+d}:L{l}_spread'] = float(max(v) - min(v))
    save('orbit', {'seed': seed, 'searched': n_rules, 'base_rule': rule_key(dec), 'base_Y3': best[0], 'rows': rows, 'spreads': dev})

# ---------------------------------------------------------------- legal environments and the certificate
def star_key(f, X2, mem, t):
    return tuple(sorted((int(REL[f[t], f[b]]), *map(int, FA[f[t]].T @ (X2[b] - X2[t]))) for b in mem))
def legal_types(dec, L0=4):
    f, X2 = supertile(dec, L0); q = (X2 - 1) // 2; key = {tuple(v): i for i, v in enumerate(q.tolist())}; types = {}
    OFF = [o for o in itertools.product((-1, 0, 1), repeat=3)]
    def star(f, X2, key, t):
        v = ((X2[t] - 1) // 2).tolist(); mem = []
        for o in OFF:
            j = key.get((v[0] + o[0], v[1] + o[1], v[2] + o[2]))
            if j is None: return None
            mem.append(j)
        return mem
    for t in range(len(f)):
        mem = star(f, X2, key, t)
        if mem is not None:
            kk = star_key(f, X2, mem, t)
            if kk not in types: types[kk] = (f[mem], X2[mem] - (X2[t] - 1), mem.index(t))   # re-centred: keys are translation invariant
    queue = list(types); n0 = len(types)
    while queue:
        fs, Xs, c = types[queue.pop()]; fi, Xi = inflate(fs, Xs, dec); qi = (Xi - 1) // 2; ki = {tuple(v): i for i, v in enumerate(qi.tolist())}
        for t in range(8 * c, 8 * c + 8):
            mem = star(fi, Xi, ki, t); assert mem is not None
            kk = star_key(fi, Xi, mem, t)
            if kk not in types: types[kk] = (fi[mem], Xi[mem] - (Xi[t] - 1), mem.index(t)); queue.append(kk)   # no coordinate growth
    return types, n0
def overlap(eta):
    return (math.pi * (1 - eta / 2) * math.sin(math.pi * eta) + 1 - math.cos(math.pi * eta)) / (math.pi ** 2 * eta)
def higham_complex(H, mu, err):
    import scipy.linalg as sl
    from scipy.sparse.csgraph import reverse_cuthill_mckee
    Hr = H.real.tocoo(); Hi = H.imag.tocoo(); n = H.shape[0]
    r = np.concatenate([2 * Hr.row, 2 * Hr.row + 1, 2 * Hi.row, 2 * Hi.row + 1]); c = np.concatenate([2 * Hr.col, 2 * Hr.col + 1, 2 * Hi.col + 1, 2 * Hi.col])
    v = np.concatenate([Hr.data, Hr.data, -Hi.data, Hi.data]); A = sps.csr_matrix((v, (r, c)), shape=(2 * n, 2 * n)); A.sum_duplicates(); A.eliminate_zeros()
    p = reverse_cuthill_mckee(A, symmetric_mode=True); A = A[p][:, p].tocoo(); N = 2 * n
    lo = A.row >= A.col; rr, cc, vv = A.row[lo], A.col[lo], A.data[lo]; bw = int((rr - cc).max())
    ab = np.zeros((bw + 1, N)); ab[rr - cc, cc] = vv; ab[0] -= mu
    try: Lb = sl.cholesky_banded(ab, lower=True, check_finite=False)
    except np.linalg.LinAlgError: return None
    if not (Lb[0] > 0).all(): return None
    u = 2.0 ** -52; fro2 = float(np.sum(Lb * Lb)) * (1 + 2 * Lb.size * u); gam = (N + 1) * u / (1 - (N + 1) * u)
    return mu - gam * fro2 * (1 + 2 * u) - err
def cmd_cert(key, theta_str, R, m, mu_str, rep='spinor'):
    """Lambda_R lower bound (and the plain D_R minimum, an upper bound) over all legal R-balls; theta = pi * theta_str"""
    dec = parse_key(key); th = math.pi * float(Fraction(theta_str)); types, n0 = legal_types(dec)
    rho = R - 0.875                                                       # r_c = sqrt(3)/2 <= 7/8
    eta = 1.0 / rho; amp = 1.0 / overlap(eta); seen = {}
    for ti, (fs, Xs, c) in enumerate(types.values()):
        f, X2 = fs, Xs
        for _ in range(m): f, X2 = inflate(f, X2, dec)
        lo = ((X2 - 1) // 2).min(0); hi = ((X2 - 1) // 2).max(0)
        cen = np.arange(c * 8 ** m, (c + 1) * 8 ** m); xc = X2[cen] / 2.0
        dmin = np.minimum((xc - lo).min(1), (hi + 1 - xc).min(1))      # distance from the centre to the patch boundary
        assert (dmin >= R + math.sqrt(3) / 2).all(), 'incomplete balls: increase m'
        for t in cen:
            d2 = ((X2 - X2[t]) ** 2).sum(1); mem = np.flatnonzero(d2 < 4 * R * R)
            rows = np.c_[REL[f[t], f[mem]], (X2[mem] - X2[t]) @ FA[f[t]]]; o = np.lexsort(rows.T[::-1])
            kb = rows[o].astype(np.int16).tobytes()
            if kb not in seen: seen[kb] = (f[mem][o], X2[mem][o])
    lows, ds = [], []
    for fb, Xb in seen.values():
        a, b, k = panels(Xb); U = spinor_links(fb, a, b, k, th)
        bl = U if rep == 'spinor' else adjoint(U).astype(complex)
        Ha = operator(len(fb), a, b, bl, w=np.full(len(a), amp)); Hp = operator(len(fb), a, b, bl)
        err = 6 * amp * 4 * 2.0 ** -52 * (1 if abs(th - math.pi / 2) < 1e-12 else 4)   # rounding of amp and (generic theta) of the links
        lows.append(higham_complex(Ha, float(Fraction(math.floor(Fraction(mu_str) * 2 ** 20), 2 ** 20)), err)); ds.append(bottom(Hp))
    ok = all(x is not None for x in lows)
    rec = {'rule': key, 'theta': theta_str, 'rep': rep, 'R': R, 'm': m, 'types': len(types), 'types_T4': n0, 'balls': len(seen), 'rho': rho, 'amplification': amp,
           'eps_rho': 6 * (amp - 1), 'mu': mu_str, 'all_certified': ok, 'Lambda_R_certified': min(lows) if ok else None, 'D_R_float': min(ds)}
    log(rec); d = json.load(open(OUT)) if os.path.exists(OUT) else {}
    d.setdefault('certs', []).append(rec); json.dump(d, open(OUT, 'w'), indent=1, default=float)
    return rec

def cmd_theta(key, L):
    dec = parse_key(key); rows = []
    for den in (2, 3, 4, 6, 8, 16, 32):
        th = math.pi / den; r = {'theta': f'pi/{den}', 'theta_value': th}
        r['pinned'] = level_bottoms(dec, L, th); r['free'] = level_bottoms(dec, L, th, free=True); rows.append(r); log(r)
    save('theta_' + key, {'L': L, 'rows': rows})

def cmd_flat():
    dec = [fid(np.eye(3, dtype=np.int64))] * 8
    out = {l: level_bottoms(dec, l, math.pi / 2) for l in (1, 2, 3)}
    save('flat_identity_rule', {'levels': out, 'note': 'all frames equal: every link is (sigma.u)^2 = 1, the connection is trivial, E_* = 0'})
    log(out)

if __name__ == '__main__':
    os.environ.setdefault('OMP_NUM_THREADS', '1'); c = sys.argv[1]
    if c == 'orbit': cmd_orbit(int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]))
    elif c == 'cert': cmd_cert(sys.argv[2], sys.argv[3], int(sys.argv[4]), int(sys.argv[5]), sys.argv[6], *(sys.argv[7:8]))
    elif c == 'theta': cmd_theta(sys.argv[2], int(sys.argv[3]))
    elif c == 'flat': cmd_flat()
