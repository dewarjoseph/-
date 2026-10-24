#!/usr/bin/env python3
"""Phase X: the localization (IMS) bounds of Phase VII Theorem 7.1 for an ARBITRARY proper decoration r.

  Lambda_R(r) := min over legal R-balls B of lambda_min((24 - A~_rho)|_B)   <=  E_*(r)  <=  D_R(r) := min_B lambda_min((24 - A)|_B)
with B_t = {a : |x_a - x_t| < R}, x = T + (13/14) G(1,1,1) (tile centroid), rho = R - 311/175, and amplified links
A~_ab = A_ab / c(|x_a - x_b| / rho), c(eta) = [pi (1 - eta/2) sin(pi eta) + 1 - cos(pi eta)] / (pi^2 eta).  The proof of Thm 7.1
uses only legality of the balls, minimality and the geometry, so it applies to every decoration (its constants are geometric).

Enumeration: every tile of a hull element is a level-m descendant of a tile whose 1-star is legal, so the legal R-balls are
the balls of the tiles of the central level-m supertile of sigma^m(tau), tau over the legal 1-star types: those of the level-5
supertile closed under Phi (phi_closed_types; the level-5 supertile alone misses rare types for most decorations, though not
for FR30 or 1387), which is the set of all legal 1-stars when the frame substitution is primitive (frame_primitivity).
Each ball is ACCEPTED only if every lattice cube whose centre lies
within R + r_c of x_t is owned by a tile of the patch (then no tile outside the patch can have its centroid within R).
Balls are deduplicated by their relative poses.  Certification of Lambda_R: every distinct ball is certified at a common
dyadic mu below the float minimum by a floating (LAPACK) Cholesky of the real form of (24 - A~) - mu with Higham's Thm 10.3 bound,
plus the entrywise error of the amplification factors (computed at 50 digits with mpmath, rounded to float64).
Prescribed-mu mode (fifth argument, a decimal): no float pass; every ball is certified directly at the dyadic mu below it, which
proves Lambda_R >= mu - (rounding bound) when all balls pass (D_R is not computed; failing balls report their float bottom).
GPU (prescribed-mu mode with IMS_GPU=1, run with a CUDA build of torch, e.g. the venv C:/Users/super/.venvs/qisgpu, torch
2.11+cu128 on the RTX 5080): CPU workers build the sparse ball operators and the main process certifies each one on the GPU
(gpu_cert: float64 cuSOLVER Cholesky, Higham bound with u = 4 * 2^-53); about 30 times faster per ball than one CPU core.
Usage: python -u -I audit/phase10_ims.py <class> <R> [m] [nproc] [mu] -> appends to audit/results/phase10_ims.jsonl"""
import os, sys, json, time, math, types, collections
from fractions import Fraction
sys.modules.setdefault('resource', types.SimpleNamespace(getrusage=lambda *a: types.SimpleNamespace(ru_maxrss=0), RUSAGE_SELF=0))
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); RES = os.path.join(HERE, 'results')
import numpy as np, scipy.sparse as sps
import phase9_pair as P9
import phase10_census as C
T0 = time.time()
def log(*a): print(f"[{time.time()-T0:7.0f}s]", *a, flush=True)
RC = 311 / 175; RC_TRUE = math.sqrt(619) / 14

def centroids(G, T): return T + (13 / 14) * (G @ np.ones(3))
def c_overlap(eta):
    import mpmath as mp
    mp.mp.dps = 50; e = mp.mpf(eta); pi = mp.pi
    return (pi * (1 - e / 2) * mp.sin(pi * e) + 1 - mp.cos(pi * e)) / (pi ** 2 * e)

def enumerate_balls(dec, R, m):
    """distinct legal R-balls of the decoration: list of (G, T) arrays.  Completeness (as in Phase VII): every tile a with
    |x_a - x_t| < R has its centroid in a cube within Chebyshev distance R of the cube containing x_t, and that cube is owned
    by a; so if every cube within Chebyshev distance R of the central supertile is owned by a tile of the patch, every ball of
    a central-supertile tile is complete.  This is checked once per 1-star type (a Chebyshev dilation); with 2^m >= R it holds,
    and any failure is counted (and must be 0)."""
    from scipy.spatial import cKDTree
    from scipy.ndimage import maximum_filter
    types_, n5 = phi_closed_types(dec); balls, rejected = {}, 0
    for G, T, c in types_.values():
        for _ in range(m): G, T = P9.inflate(G, T, dec)
        X14 = 14 * T + 13 * G.sum(-1); tree = cKDTree(X14.astype(float))
        Cc = (np.einsum('nij,uj->nui', G, P9.BASE) + 2 * T[:, None, :] - 1) // 2; lo = Cc.reshape(-1, 3).min(0) - R; shp = Cc.reshape(-1, 3).max(0) - lo + 1 + R
        grid = -np.ones(tuple(shp), dtype=np.int64); grid[tuple((Cc - lo).reshape(-1, 3).T)] = np.repeat(np.arange(len(G)), 7)
        central = np.zeros(tuple(shp), bool); cs = (Cc[c * 8 ** m:(c + 1) * 8 ** m] - lo).reshape(-1, 3); central[tuple(cs.T)] = True
        region = maximum_filter(central, size=2 * R + 1, mode='constant', cval=False)
        if (region & (grid < 0)).any(): rejected += 8 ** m; continue
        ts = np.arange(c * 8 ** m, (c + 1) * 8 ** m); near = tree.query_ball_point(X14[ts].astype(float), 14 * R + 1e-6)
        for t2, cand in zip(ts, near):
            cand = np.array(cand); d2 = ((X14[cand] - X14[t2]) ** 2).sum(1); mem2 = np.sort(cand[d2 < 196 * R * R]); Gt = G[t2]
            rel = np.c_[np.einsum('ji,njk->nik', Gt, G[mem2]).reshape(len(mem2), 9), (X14[mem2] - X14[t2]) @ Gt]
            k2 = rel[np.lexsort(rel.T[::-1])].astype(np.int8).tobytes()
            if k2 not in balls: balls[k2] = (G[mem2].copy(), T[mem2].copy())
    return list(balls.values()), types_, n5, rejected

def phi_closed_types(dec):
    """the legal 1-star types {key: (G, T, index of the central tile)}: those of the level-5 supertile, closed under Phi (the
    1-stars of the children of the central tile, read inside sigma(tau), as in phase10_census.record); and the level-5 count"""
    S5 = P9.build([dec] * 5); G5, T5 = S5['G'], S5['T']; types_ = {}
    for t, mem in C.stars_of(S5): types_.setdefault(C.star_key(G5, T5, mem, t), (G5[mem], T5[mem], mem.index(t)))
    n5 = len(types_); keys = list(types_); i = 0
    while i < len(keys):
        G, T, c = types_[keys[i]]; Gi, Ti = P9.inflate(G, T, dec); _, _, grid, lo = C.patch_ops(Gi, Ti); N = np.array(grid.shape); i += 1
        ch = np.arange(8 * c, 8 * c + 8); Cc = (np.einsum('nij,oj->noi', Gi[ch], 2 * P9.OFF1 + 1) + 2 * Ti[ch][:, None, :] - 1) // 2 - lo
        for j, tt in enumerate(ch):
            q = Cc[j]; assert ((q >= 0) & (q < N)).all(); own = grid[q[:, 0], q[:, 1], q[:, 2]]; assert (own >= 0).all(), 'closure lemma violated'
            mem = sorted(set(own.tolist())); k = C.star_key(Gi, Ti, mem, int(tt))
            if k not in types_: types_[k] = (Gi[mem], Ti[mem], mem.index(int(tt))); keys.append(k)
    return types_, n5

def frame_primitivity(dec):
    """the frame substitution matrix M[g h_c, g] (children of a tile with frame g have frames g h_c) on the frames reachable from
    the identity; returns (number of frames, smallest k with M^k > 0, or None).  Primitivity makes the forward Phi-orbit of any
    legal 1-star equal to the set of all legal 1-stars (Phase VII s.6.1), which with Phi-closure of the enumerated set gives
    completeness of the ball enumeration."""
    hs = [g for g, _ in P9.ops(dec)]; key = lambda M: tuple(M.ravel().tolist()); frames = {key(np.eye(3, dtype=np.int64)): np.eye(3, dtype=np.int64)}; todo = list(frames.values())
    while todo:
        g = todo.pop()
        for h in hs:
            gh = g @ h
            if key(gh) not in frames: frames[key(gh)] = gh; todo.append(gh)
    idx = {k: i for i, k in enumerate(frames)}; n = len(frames); M = np.zeros((n, n), dtype=np.int64)
    for k, g in frames.items():
        for h in hs: M[idx[key(g @ h)], idx[k]] += 1
    P = np.eye(n, dtype=np.int64)
    for k in range(1, n * n + 2):
        P = np.minimum(P @ M, 1)
        if (P > 0).all(): return n, k
    return n, None

def ball_matrices(G, T, rho, amp, plain=True, dense=True):
    """pinned operator 24 - A (unless plain is False) and the amplified 24 - A~ on a ball (dense arrays, or summed CSR matrices);
    amp maps rounded 14*distance^2 to 1/c(d/rho)"""
    Cc = (np.einsum('nij,uj->nui', G, P9.BASE) + 2 * T[:, None, :] - 1) // 2; lo = Cc.reshape(-1, 3).min(0); Cc = Cc - lo
    grid = -np.ones(tuple(Cc.reshape(-1, 3).max(0) + 1), dtype=np.int64); grid[tuple(Cc.reshape(-1, 3).T)] = np.repeat(np.arange(len(G)), 7)
    a, b, ax = P9.panels(grid); n = len(G); X = centroids(G, T)
    U = P9.links(G, a, b, ax); d2 = np.round(196 * ((X[a] - X[b]) ** 2).sum(1)).astype(int)
    w = np.array([amp[v] for v in d2])
    def build(scale):
        r = np.concatenate([2 * a[:, None] + np.array([0, 0, 1, 1]), 2 * b[:, None] + np.array([0, 0, 1, 1])]).ravel()
        cidx = np.concatenate([2 * b[:, None] + np.array([0, 1, 0, 1]), 2 * a[:, None] + np.array([0, 1, 0, 1])]).ravel()
        Us = U * scale[:, None, None]; v = np.concatenate([Us.reshape(-1, 4), np.conj(np.transpose(Us, (0, 2, 1))).reshape(-1, 4)]).ravel()
        Hs = (24 * sps.identity(2 * n) - sps.csr_matrix((v, (r, cidx)), shape=(2 * n, 2 * n))).tocsr(); Hs.sum_duplicates()
        return Hs.toarray() if dense else Hs
    return (build(np.ones(len(a))) if plain else None), build(w), d2

def chol_cert(A, mu):
    """the Higham certificate for the symmetric matrix A = M - mu (both triangles filled; overwritten): LAPACK dpotrf, then
    lambda_min(M) >= mu - gamma_{N+1} ||L||_F^2 (1 + 2(N^2 + 1)u) * 1.0001, or None when the factorization breaks down.
    Higham (2002) Thm 10.3, |dA| <= gamma_{N+1} |L||L^T|, holds for every order of evaluating the inner products, hence for
    blocked LAPACK with conventional (non-Strassen) matrix multiplication in IEEE double; it agrees with Phase VII's column
    algorithm (phase9_pair.cholesky_lower) to 1e-13 on these matrices and is 5-8 times faster."""
    import scipy.linalg.lapack as la
    N = A.shape[0]; c, info = la.dpotrf(A.T, lower=1, overwrite_a=1, clean=0)    # A.T: the Fortran-ordered view of the symmetric A
    if info != 0: return None
    gam = (N + 1) * P9.U_ROUND / (1 - (N + 1) * P9.U_ROUND); fro2 = sum(float(c[j:, j] @ c[j:, j]) for j in range(N))
    return float(mu) - gam * fro2 * (1 + 2 * (N * N + 1) * P9.U_ROUND) * 1.0001

def cert_lower(Hd, mu, entry_err):
    """the certificate for the real form of Hd - mu, plus the entrywise error of Hd"""
    n = Hd.shape[0]; N = 2 * n; A = np.empty((N, N)); A[:n, :n] = Hd.real; A[n:, n:] = Hd.real; A[:n, n:] = -Hd.imag; A[n:, :n] = Hd.imag
    A[np.arange(N), np.arange(N)] -= float(mu); low = chol_cert(A, mu)
    return None if low is None else low - entry_err

def cert_lower_sparse(H, mu):
    """phase9_pair.certified_lower (Gaussian-integer H, dyadic mu: H - mu exact) with one dense real matrix in memory: the real form
    is filled block by block from the sparse matrix and factored in place (as cert_lower); for the level-4 enclosures"""
    n = H.shape[0]; N = 2 * n; A = np.empty((N, N)); Re = H.real.toarray(); assert np.array_equal(Re, np.rint(Re)); A[:n, :n] = Re; A[n:, n:] = Re; del Re
    Im = H.imag.toarray(); assert np.array_equal(Im, np.rint(Im)); A[:n, n:] = -Im; A[n:, :n] = Im; del Im
    A[np.arange(N), np.arange(N)] -= float(mu); return chol_cert(A, mu)

def work(args):
    """mu None: the float bottoms of the plain and amplified ball operators; mu given: the certificate only (work_at)"""
    G, T, rho, amp, mu, amp_err = args
    if mu is not None: return (None, None, work_at(args)[0])
    Hp, Ha, d2 = ball_matrices(G, T, rho, amp)
    if Hp.shape[0] <= 800: lp = float(np.linalg.eigvalsh(Hp)[0]); la = float(np.linalg.eigvalsh(Ha)[0])
    else:
        import scipy.sparse.linalg as sla
        lp = float(sla.eigsh(sps.csr_matrix(Hp), k=2, which='SA', tol=1e-12, ncv=40, return_eigenvectors=False).min())
        la = float(sla.eigsh(sps.csr_matrix(Ha), k=2, which='SA', tol=1e-12, ncv=40, return_eigenvectors=False).min())
    return lp, la, None

U_GPU = 4 * 2.0 ** -53

def ball_csr(args):
    """the amplified ball operator as summed CSR arrays: small to send to the GPU process (its dense form is entry-for-entry the
    matrix of the CPU path)"""
    G, T, rho, amp = args; Hs = ball_matrices(G, T, rho, amp, plain=False, dense=False)[1]
    return Hs.shape[0], Hs.indptr, Hs.indices, Hs.data

def gpu_cert(n, indptr, indices, data, mu, entry_err):
    """chol_cert on the GPU (torch float64, cuSOLVER potrf through cholesky_ex) for the real form of the Hermitian CSR operator minus
    mu, assembled on the device by exact copies of its entries.  The Higham bound is applied with u = 4 * 2^-53: a margin of four
    ulps per operation, which covers IEEE double in any summation order (with or without FMA) and a vendor division or square
    root that is not correctly rounded.  Returns (certified lower bound or None, float bottom of the operator when it fails)."""
    import torch
    N = 2 * n; dev = 'cuda'
    rows = torch.from_numpy(np.repeat(np.arange(n, dtype=np.int64), np.diff(indptr))).to(dev); cols = torch.from_numpy(indices.astype(np.int64)).to(dev)
    re = torch.from_numpy(np.ascontiguousarray(data.real)).to(dev); im = torch.from_numpy(np.ascontiguousarray(data.imag)).to(dev)
    A = torch.zeros((N, N), dtype=torch.float64, device=dev)
    A[rows, cols] = re; A[rows + n, cols + n] = re; A[rows, cols + n] = -im; A[rows + n, cols] = im
    A.diagonal().sub_(float(mu)); L, info = torch.linalg.cholesky_ex(A)
    if int(info) != 0:
        A.diagonal().add_(float(mu)); lam = float(torch.linalg.eigvalsh(A)[0]); return None, lam
    u = U_GPU; gam = (N + 1) * u / (1 - (N + 1) * u); fro2 = float(torch.tril(L).square().sum())
    return float(mu) - gam * fro2 * (1 + 2 * (N * N + 1) * u) * 1.0001 - entry_err, None

def work_at(args):
    """the certificate at mu only (no eigensolve); the float bottom of the amplified ball only if it fails.  Entry error of the
    amplified matrix: each panel link is scaled by a float with relative error <= amp_err, and row sums are <= 24 * max amp"""
    G, T, rho, amp, mu, amp_err = args
    _, Ha, _ = ball_matrices(G, T, rho, amp, plain=False); low = cert_lower(Ha, mu, amp_err * 24 * max(amp.values()))
    return low, (None if low is not None else float(np.linalg.eigvalsh(Ha)[0]))

if __name__ == '__main__':
    import multiprocessing as mp
    ext = sys.argv[1].startswith('x'); cls, R = int(sys.argv[1].lstrip('x')), int(sys.argv[2])      # 'x<j>': extended (stage C) index j
    m = int(sys.argv[3]) if len(sys.argv) > 3 else max(1, math.ceil(math.log2(R)))
    nproc = int(sys.argv[4]) if len(sys.argv) > 4 else 8
    mu_at = Fraction(sys.argv[5]) if len(sys.argv) > 5 else None              # prescribed-mu mode: certify Lambda_R >= mu_at directly
    if ext:
        import phase10_improper as X
        dec = X.dec_of(cls)
    else: dec = P9.decoration(cls)
    rho = Fraction(R) - Fraction(311, 175)
    t0 = time.time(); balls, types_, n5, rej = enumerate_balls(dec, R, m); ntypes = len(types_)
    log(f"class {cls} R={R} m={m}: {ntypes} 1-star types ({n5} in T5), {len(balls)} distinct balls, {rej} incomplete balls rejected ({time.time()-t0:.0f}s)")
    assert rej == 0, 'a ball of a central-supertile tile is incomplete: increase m'
    nfr, kprim = frame_primitivity(dec); log(f'frame substitution: {nfr} frames, primitive with M^{kprim} > 0' if kprim else f'frame substitution NOT primitive ({nfr} frames)')
    # the squared centroid distances of panel-adjacent tiles form a small geometric set: those of the panels of the legal 1-stars
    # (every panel is a central-tile panel of the 1-star of either of its tiles)
    d2s = set()
    for G, T, _ in types_.values():
        X14 = 14 * T + 13 * G.sum(-1); a_, b_, _ = P9.panels(C.patch_ops(G, T)[2]); d2s |= set(((X14[a_] - X14[b_]) ** 2).sum(1).tolist())
    for G, T in balls[:50]:
        Xb = 14 * T + 13 * G.sum(-1); Cc = (np.einsum('nij,uj->nui', G, P9.BASE) + 2 * T[:, None, :] - 1) // 2; lo = Cc.reshape(-1, 3).min(0)
        grid = -np.ones(tuple(Cc.reshape(-1, 3).max(0) - lo + 1), dtype=np.int64); grid[tuple((Cc - lo).reshape(-1, 3).T)] = np.repeat(np.arange(len(G)), 7)
        a_, b_, _ = P9.panels(grid); assert set(((Xb[a_] - Xb[b_]) ** 2).sum(1).tolist()) <= d2s
    amp = {v: float(1 / c_overlap(math.sqrt(v) / 14 / float(rho))) for v in sorted(d2s)}; amp_err = 4 * 2 ** -53
    sizes = [len(G) for G, _ in balls]
    rec = {('extended_index' if ext else 'class'): cls, 'R': R, 'm': m, 'rho': f'{rho.numerator}/{rho.denominator}', 'one_star_types': ntypes, 'one_star_types_T5': n5,
           'distinct_balls': len(balls), 'rejected_incomplete': rej, 'ball_tiles': [min(sizes), max(sizes)], 'frames': nfr, 'primitive_power': kprim}
    if ext: rec.update({'class': None, 'decoration': {str(k): list(v) for k, v in dec.items()}})
    if mu_at is None:
        with mp.Pool(nproc) as pool:
            res = pool.map(work, [(G, T, float(rho), amp, None, amp_err) for G, T in balls], chunksize=4)
            lp = np.array([r[0] for r in res]); la = np.array([r[1] for r in res])
            mu = Fraction(math.floor((la.min() - 1e-6) * 2 ** 20), 2 ** 20)
            cert = pool.map(work, [(G, T, float(rho), amp, mu, amp_err) for G, T in balls], chunksize=4)
        lows = [r[2] for r in cert]; ok = all(x is not None for x in lows)
        # D_R is an upper bound on E_* (every legal ball is a legal patch); certify it by the exact Rayleigh quotient on the minimising ball
        G, T = balls[int(lp.argmin())]; q = P9.rayleigh_upper(ball_matrices(G, T, float(rho), amp, plain=True, dense=False)[0])
        rec.update({'D_R_float': float(lp.min()), 'D_R_upper_exact': f'{q.numerator}/{q.denominator}', 'D_R_upper': float(q), 'Lambda_R_float': float(la.min()),
                    'mu': f'{mu.numerator}/{mu.denominator}', 'Lambda_R_certified': min(lows) if ok else None, 'all_balls_certified': ok})
    else:
        mu = Fraction(math.floor(mu_at * 2 ** 20), 2 ** 20)
        if os.environ.get('IMS_GPU'):                                             # CPU workers build the sparse operators, the GPU certifies
            import torch
            err = amp_err * 24 * max(amp.values()); res = []
            with mp.Pool(nproc) as pool:
                for i, (n, ip, ix, dt) in enumerate(pool.imap(ball_csr, [(G, T, float(rho), amp) for G, T in balls], chunksize=4)):
                    res.append(gpu_cert(n, ip, ix, dt, mu, err))
                    if i % 500 == 0: log(f"{i + 1}/{len(balls)} balls certified on the GPU, {sum(r[0] is None for r in res)} failed")
            rec['certificate_device'] = f"{torch.cuda.get_device_name(0)}, torch {torch.__version__}, float64 cholesky_ex, Higham bound with u = 4 * 2^-53"
        else:
            with mp.Pool(nproc) as pool: res = pool.map(work_at, [(G, T, float(rho), amp, mu, amp_err) for G, T in balls], chunksize=2)
        fails = sorted(r[1] for r in res if r[0] is None); ok = not fails
        rec.update({'mode': 'prescribed mu (no float pass; D_R not computed)', 'mu': f'{mu.numerator}/{mu.denominator}', 'mu_float': float(mu),
                    'Lambda_R_certified': min(r[0] for r in res) if ok else None, 'all_balls_certified': ok, 'balls_failing': len(fails),
                    'failing_lambda_tilde_float_lowest': fails[:20]})
    rec['seconds'] = time.time() - T0; log(rec)
    with open(os.path.join(RES, 'phase10_ims.jsonl'), 'a') as f: f.write(json.dumps(rec) + '\n')
