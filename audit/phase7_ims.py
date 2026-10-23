#!/usr/bin/env python3
"""Phase VII (I, added after the frozen protocol -- labelled as such in the report): localization (IMS) lower bound on
E(Y) = inf spec(24 - A_U) for every tiling Y whose R-stars are legal FR30 R-stars.

Exact IMS identity (proved in deliverables/PHASE7_REPORT.md, section 7).  x_a = centroid of chair a; phi = Dirichlet ground
state of the ball B_rho in R^3; chi_y(a) = phi(x_a - y)/||phi||_2.  Then  int chi_y(a)^2 dy = 1  and  int chi_y(a) chi_y(b) dy =
c(|x_a - x_b|/rho)  with  c(eta) = [pi (1 - eta/2) sin(pi eta) + 1 - cos(pi eta)] / (pi^2 eta)  (0 < eta <= 1), so that
    24 - A_U  =  int chi_y (24 - A~) chi_y dy,      A~_ab = A_ab / c(|x_a - x_b|/rho)     (exact operator identity),
and for every tiling Y,  E(Y) >= inf_t lambda_min( (24 - A~) restricted to {a : |x_a - x_t| < rho + r_c} ),  r_c = sqrt(619)/14
(largest distance from a chair's centroid to a point of the chair).  With R >= rho + r_c that ball lies inside the R-star of t, so
    L_R := min over legal R-stars of lambda_min((24 - A~)|ball)   is a lower bound on E(Y) for every Y in T_R,
and, since (24 - A)|ball is a principal submatrix of FR30's operator,  E_FR30 - eps(rho) <= E_inf(R) <= E_FR30  with
eps(rho) = max over legal 1-stars of sum_{24 panels} (1/c(|h_f|/rho) - 1) ~ pi^2 S_1/(6 rho^2),  S_1 = max sum |h_f|^2.

Computation.  Every FR30 tile t is a descendant, m = ceil(log2 R) levels down, of a tile whose 1-star tau is legal (|V_1| = 72);
its R-star is read off sigma^m(tau), and completeness of that R-star inside the patch is asserted for every t (so the
enumeration of ball patches is complete without further lemmas).  lambda_min of every distinct ball is certified >= mu_R - delta
by a floating-point Cholesky of the real form of the stored float matrix minus mu_R (row-oriented, BLAS-2 inner products;
Higham 2002 Thm 10.3: R^T R = M + dM, |dM| <= gamma_{N+1}|R^T||R|, so ||dM||_2 <= gamma_{N+1} ||R||_F^2), plus the entrywise
error of the stored amplification factors (mpmath interval arithmetic).  mu_R is a dyadic rational just below the smallest
float lambda_min.  The unamplified (24 - A)|ball minima are certified the same way (exact Bareiss cross-check at the smallest R).
Usage: python -u -I audit/phase7_ims.py R [R ...]  -> audit/results/phase7_ims.json (merged per R)"""
import os, sys, time, json, math, itertools, collections
from fractions import Fraction
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); RES = os.path.join(HERE, 'results')
import numpy as np
T0 = time.time()
def log(*a): print(f"[{time.time()-T0:7.0f}s]", *a, flush=True)
U_ROUND = 2.0 ** -53
RC_UP = Fraction(311, 175)                       # > r_c = sqrt(619)/14 = 1.7771227...  (311/175 = 1.7771428...)
assert RC_UP ** 2 > Fraction(619, 196)

def amp_table(d2s, rho):
    """1/c(|h|/rho) for |14 h|^2 = d2 in d2s, by mpmath interval arithmetic: {d2: (stored float, rigorous error bound)}."""
    from mpmath import iv
    iv.dps = 40; r = iv.mpf(rho.numerator) / rho.denominator; out = {}
    for d2 in sorted(set(int(x) for x in d2s)):
        eta = iv.sqrt(iv.mpf(d2)) / 14 / r; assert eta.b < 1, "closed form of c(eta) used here needs |h| < rho"
        pe = iv.pi * eta; c = (iv.pi * (1 - eta / 2) * iv.sin(pe) + 1 - iv.cos(pe)) / (iv.pi ** 2 * eta); a = 1 / c
        lo, hi = float(a.a) * (1 - 4 * U_ROUND), float(a.b) * (1 + 4 * U_ROUND); val = 0.5 * (lo + hi)
        out[d2] = (val, (hi - lo) + 4 * U_ROUND * hi)
    return out

def centroid14(G, T):
    """14 x centroid: x = T + G (13/14)(1,1,1)  (chair = unit cubes u + [0,1]^3, u in {0,1}^3 minus (1,1,1), mean u = 3/7)"""
    return 14 * np.asarray(T, np.int64) + 13 * np.asarray(G, np.int64).sum(-1)

def ball_coo(k, rho=None):
    """24 - A_U (rho None) or 24 - A~_rho restricted to the ball patch with key k, as COO data of the complex Hermitian matrix
    (dim 2n) plus err = bound on the real-form row sums of |stored - exact| (0 when rho is None: Gaussian-integer entries)."""
    import phase7_local as P
    poses, center = P.poses_from_key(k); own = P.owner_dict(poses); fidx = [P.gidx[P.key(g)] for g, t in poses]; n = len(poses)
    X = centroid14(np.array([g for g, t in poses]), np.array([t for g, t in poses]))
    blocks = collections.defaultdict(lambda: np.zeros((2, 2), complex))
    for q, t1 in own.items():
        for ax in range(3):
            q2 = (q[0] + (ax == 0), q[1] + (ax == 1), q[2] + (ax == 2)); t2 = own.get(q2)
            if t2 is None or t2 == t1: continue
            C = P.LINKGI[fidx[t1], fidx[t2], ax]; C = C[..., 0] + 1j * C[..., 1]
            blocks[(t1, t2)] -= C; blocks[(t2, t1)] -= C.conj().T
    amp = None; err = 0.0
    if rho is not None:
        d2 = {pr: int(((X[pr[0]] - X[pr[1]]) ** 2).sum()) for pr in blocks}; amp = amp_table(d2.values(), rho)
        err = 24 * max(e + 2 * U_ROUND * v for v, e in amp.values())       # <= 24 panels per row, one unit real-form entry each
    rows, cols, vals = list(range(2 * n)), list(range(2 * n)), [24.0 + 0j] * (2 * n)
    for (a, b), M in blocks.items():
        f = 1.0 if amp is None else amp[d2[(a, b)]][0]
        for i in range(2):
            for j in range(2):
                if M[i, j] != 0: rows.append(2 * a + i); cols.append(2 * b + j); vals.append(complex(f * M[i, j].real, f * M[i, j].imag))
    return np.array(rows), np.array(cols), np.array(vals), 2 * n, err

def ball_H(k, rho=None):
    """dense (Re, Im, err); integer dtype when rho is None (used by the exact Bareiss check)."""
    r, c, v, N, err = ball_coo(k, rho)
    Re = np.zeros((N, N)); Im = np.zeros((N, N)); np.add.at(Re, (r, c), v.real); np.add.at(Im, (r, c), v.imag)
    if rho is None: Re = np.rint(Re).astype(np.int64); Im = np.rint(Im).astype(np.int64)
    return Re, Im, err

def _rho(s): return None if s is None else Fraction(s)

def lam_min(args):
    """float lambda_min (sparse Lanczos; diagnostic only, used to place the certified threshold)."""
    import scipy.sparse as sps, scipy.sparse.linalg as sla
    k, rho = args; r, c, v, N, _ = ball_coo(k, _rho(rho)); H = sps.csr_matrix((v, (r, c)), shape=(N, N))
    return float(sla.eigsh(H, k=1, which='SA', tol=1e-12, maxiter=20000, return_eigenvectors=False)[0])

def cholesky_lower(A, nb=96):
    """in-place blocked right-looking Cholesky of the lower triangle of A (float64): explicit divisions by the pivots, panel
    columns by BLAS-2 inner products, trailing update by conventional GEMM -- every computed entry is
    (a_ij - sum_k l_ik l_jk)/l_jj with the sum evaluated in some order, so Higham 2002 Thm 10.3 applies.  Returns ok."""
    N = A.shape[0]
    for k in range(0, N, nb):
        e = min(k + nb, N)
        for j in range(k, e):
            s = A[j, j] - A[j, k:j] @ A[j, k:j]
            if not s > 0: return False
            A[j, j] = math.sqrt(s)
            if j + 1 < N: A[j + 1:, j] = (A[j + 1:, j] - A[j + 1:, k:j] @ A[j, k:j]) / A[j, j]
        if e < N:
            Pn = A[e:, k:e]; A[e:, e:] -= Pn @ Pn.T                          # upper-triangle garbage is never read
    return True

def cholesky_certify(args):
    """(ok, delta): if ok, lambda_min of the exact restricted operator >= mu - delta (Higham Thm 10.3, ||L||_F^2, entry errors)."""
    k, mu, rho = args
    r, c, v, N2, err = ball_coo(k, _rho(rho)); N = 2 * N2; A = np.zeros((N, N))
    np.add.at(A, (r, c), v.real); np.add.at(A, (r + N2, c + N2), v.real); np.add.at(A, (r, c + N2), -v.imag); np.add.at(A, (r + N2, c), v.imag)
    A[np.arange(N), np.arange(N)] -= float(mu)                              # exact: 24 minus a 20-bit dyadic < 24
    A = np.tril(A)
    if not cholesky_lower(A): return (False, None)
    L = np.tril(A); gam = (N + 1) * U_ROUND / (1 - (N + 1) * U_ROUND)
    fro2 = float(np.sum(L * L)) * (1 + 2 * (N * N + 1) * U_ROUND)          # rounding of the sum of squares
    return (True, gam * fro2 * 1.0001 + err)

def legal_1stars():
    import phase7_local as P
    G4, T4 = P.gen_poses(4); grid4 = P.owner_grid(4, G4, T4); cnt1, _ = P.star_types(G4, T4, grid4, P.LODD[1])
    seed = max(cnt1, key=cnt1.get); V1 = {seed}; frontier = [seed]
    while frontier:
        new = []
        for k in frontier:
            for kk in P.Phi_r(k, P.LODD[1]):
                if kk not in V1: V1.add(kk); new.append(kk)
        frontier = new
    assert len(V1) == 72 and set(cnt1) <= V1
    return V1

def geometry_constants(V1):
    """r_c^2 and, per legal 1-star, the 24 squared panel distances |14 (x_b - x_a)|^2 of the centre tile."""
    import phase7_local as P
    from independent_clifford_q8_audit import U3
    ub = [Fraction(sum(u[i] for u in U3), 7) + Fraction(1, 2) for i in range(3)]; assert ub == [Fraction(13, 14)] * 3
    verts = {tuple(u[i] + d[i] for i in range(3)) for u in U3 for d in itertools.product((0, 1), repeat=3)}
    rc2 = max(sum((v[i] - ub[i]) ** 2 for i in range(3)) for v in verts); assert rc2 == Fraction(619, 196)
    D = {}
    for k in V1:
        poses, c = P.poses_from_key(k); own = P.owner_dict(poses)
        G = np.array([g for g, t in poses]); T = np.array([t for g, t in poses]); X = centroid14(G, T); d = []
        for q in P.cubes_of_poses(G[c:c+1], T[c:c+1])[0]:
            q = tuple(int(x) for x in q)
            for ax in range(3):
                for sg in (1, -1):
                    q2 = list(q); q2[ax] += sg; b = own.get(tuple(q2)); assert b is not None
                    if b != c: d.append(int(((X[b] - X[c]) ** 2).sum()))
        assert len(d) == 24; D[k] = d
    return rc2, D

def enumerate_balls(V1, R):
    """distinct ball patches {a : |x_a - x_t| < R} of FR30 tiles t, keyed by relative poses (as in phase7_local.encode)."""
    import phase7_local as P
    from scipy.spatial import cKDTree
    m = max(1, math.ceil(math.log2(R))); odd = 2 * np.array(P.Lr(R)) + 1; balls = collections.Counter(); sizes = []
    for k in sorted(V1, key=lambda z: sorted(z)):
        poses, center = P.poses_from_key(k)
        for _ in range(m): poses = P.inflate(poses)
        G = np.array([g for g, t in poses], np.int64); T = np.array([t for g, t in poses], np.int64); n = len(G)
        cubes = P.cubes_of_poses(G, T); lo = cubes.reshape(-1, 3).min(0); shp = cubes.reshape(-1, 3).max(0) - lo + 1
        grid = np.full(tuple(shp), -1, np.int32); cc = cubes.reshape(-1, 3) - lo
        assert (grid[cc[:, 0], cc[:, 1], cc[:, 2]] == -1).all(); grid[cc[:, 0], cc[:, 1], cc[:, 2]] = np.repeat(np.arange(n, dtype=np.int32), 7)
        fi = P.frame_index(G); X = centroid14(G, T); tree = cKDTree(X.astype(float))
        desc = np.arange(center * 8 ** m, (center + 1) * 8 ** m)
        for s in range(0, len(desc), 64):
            ts = desc[s:s + 64]
            Q = P.cubes_of_poses(G[ts], T[ts], odd) - lo; inside = ((Q >= 0) & (Q < shp)).all(-1)
            assert inside.all(), 'R-star leaves sigma^m(1-star)'
            O = grid[Q[..., 0], Q[..., 1], Q[..., 2]]; assert (O >= 0).all(), 'R-star incomplete inside sigma^m(1-star)'
            near = tree.query_ball_point(X[ts].astype(float), r=14 * R + 1e-6)
            for i, t in enumerate(ts):
                cand = np.array(near[i]); d2 = ((X[cand] - X[t]) ** 2).sum(1); mem = cand[d2 < 196 * R * R]
                assert np.isin(mem, O[i]).all(), 'ball not inside the R-star'
                rf = P.MULT[P.INV[fi[t]], fi[mem]]; rel = (G[t].T @ (T[mem] - T[t]).T).T
                balls[frozenset(int(x) for x in P.encode(rf, rel))] += 1; sizes.append(len(mem))
    return balls, sizes

def certify_min(pool, keys, rho):
    """float lambda_min of every ball, then a common certified lower bound."""
    rs = None if rho is None else f'{rho.numerator}/{rho.denominator}'
    lams = dict(zip(keys, pool.map(lam_min, [(k, rs) for k in keys], chunksize=2))); kmin = min(lams, key=lams.get); lmin = lams[kmin]
    mu = Fraction(int(math.floor((lmin - 1e-6) * 2 ** 20)), 2 ** 20)
    cert = pool.map(cholesky_certify, [(k, mu, rs) for k in keys], chunksize=1)
    fails = sum(1 for ok, d in cert if not ok); assert fails == 0, f'{fails} Cholesky failures at mu = {float(mu)}'
    dmax = max(d for ok, d in cert if ok)
    return lams, kmin, mu, mu - Fraction(dmax), dmax

def run(R, V1, D, pool, exact_check=False, plain=True):
    t0 = time.time(); balls, sizes = enumerate_balls(V1, R); keys = list(balls)
    log(f"R={R}: {sum(balls.values())} tiles, {len(keys)} distinct ball patches, {min(sizes)}..{max(sizes)} tiles per ball ({time.time()-t0:.0f}s)")
    rho = R - RC_UP; res = {'R': R, 'm': max(1, math.ceil(math.log2(R))), 'tiles_enumerated': sum(balls.values()), 'distinct_balls': len(keys),
                           'ball_tiles_min': min(sizes), 'ball_tiles_max': max(sizes), 'rho': f'{rho.numerator}/{rho.denominator}'}
    amp = amp_table([d for v in D.values() for d in v], rho)
    eps = max(sum(amp[d][0] + amp[d][1] - 1 for d in v) for v in D.values()); res['eps_upper'] = eps * (1 + 1e-12)
    if plain:
        t0 = time.time(); lams, kmin, mu, lc, dmax = certify_min(pool, keys, None)
        res['plain'] = {'lambda_min_float_min': lams[kmin], 'lambda_min_float_median': float(np.median(list(lams.values()))),
                        'lambda_min_float_max': max(lams.values()), 'certified_min': f'{lc.numerator}/{lc.denominator}', 'certified_min_float': float(lc)}
        log(f"R={R}: (24 - A)|ball: lambda_min in [{lams[kmin]:.6f}, {max(lams.values()):.6f}], certified min >= {float(lc):.7f} ({time.time()-t0:.0f}s)")
        if exact_check:
            import phase7_local as P
            t1 = time.time(); Re, Im, _ = ball_H(kmin); ok = P.bareiss_posdef(Re, Im, mu.numerator, mu.denominator)
            above = Fraction(int(math.floor((lams[kmin] + 1e-6) * 2 ** 20)) + 1, 2 ** 20); rej = not P.bareiss_posdef(Re, Im, above.numerator, above.denominator)
            res['plain']['exact_bareiss_minimiser'] = {'complex_dim': int(Re.shape[0]), 'H_minus_mu_posdef': ok, 'H_minus_lambda_plus_1e-6_not_posdef': rej}
            log(f"R={R}: exact Bareiss on the minimising ball (complex dim {Re.shape[0]}): H - mu > 0 {ok}; H - (lambda+1e-6) not > 0 {rej} ({time.time()-t1:.0f}s)")
    t0 = time.time(); lams, kmin, mu, lc, dmax = certify_min(pool, keys, rho)
    res.update({'lambda_tilde_float_min': lams[kmin], 'lambda_tilde_float_median': float(np.median(list(lams.values()))), 'mu': f'{mu.numerator}/{mu.denominator}',
                'max_delta': dmax, 'L_R_certified': f'{lc.numerator}/{lc.denominator}', 'L_R_float': float(lc)})
    log(f"R={R}: CERTIFIED  E(Y) >= L_R = {float(lc):.6f} for every Y in T_{R}  (float min {lams[kmin]:.6f}, max delta {dmax:.1e}; "
        f"rho = {float(rho):.4f}, eps(rho) <= {eps:.4f}) ({time.time()-t0:.0f}s)")
    return res

if __name__ == '__main__':
    import multiprocessing as mp
    Rs = [int(x) for x in sys.argv[1:]] or [4, 6, 8]
    nproc = int(os.environ.get('IMS_PROCS', '12')); plain_max = int(os.environ.get('IMS_PLAIN_MAX', '10'))
    V1 = legal_1stars(); rc2, D = geometry_constants(V1); S1 = max(Fraction(sum(v), 196) for v in D.values())
    log(f"|V_1| = {len(V1)}; r_c^2 = {rc2}; S_1 = max sum |x_a - x_b|^2 = {S1} = {float(S1):.4f}; pi^2 S_1/6 = {math.pi ** 2 * float(S1) / 6:.4f}")
    path = os.path.join(RES, 'phase7_ims.json'); out = json.load(open(path)) if os.path.exists(path) else {}
    out['constants'] = {'r_c_squared': str(rc2), 'r_c_upper': str(RC_UP), 'S_1': str(S1), 'S_1_float': float(S1),
                        'pi2_S1_over_6': math.pi ** 2 * float(S1) / 6, 'S_over_V1_min': float(min(Fraction(sum(v), 196) for v in D.values()))}
    with mp.Pool(nproc) as pool:
        for R in Rs:
            out[str(R)] = run(R, V1, D, pool, exact_check=(R == 6), plain=(R <= plain_max))
            json.dump(out, open(path, 'w'), indent=1)
    log('done')
