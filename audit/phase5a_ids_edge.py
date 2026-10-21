#!/usr/bin/env python3
"""
Phase 5a / Task B4 (research targets H4 / H5): the integrated density of states (IDS) near the spectral edge of the
PINNED Clifford hopping operator on FR30 Chair44 patches, with matched controls.

OPERATOR (identical to audit/phase5_bulk_bottom_lobpcg.py and audit/phase5a_controls.py)
  Tiles of the level-L FR30 supertile: tiles_at_level(FR30, L) (audit/independent_clifford_q8_audit.py), n = 8^L.
  Edges = shared unit panels f = (a, b) (panel_edges; multigraph), ambient normal n_f along +x, +y or +z.
  Links C_ab = (sigma . M_a^T n_f)(sigma . M_b^T n_f) in Q8, C_ba = C_ab^dagger (unit magnitude).
  Hilbert space l^2(tiles) x C^2 (dim 2n); (A psi)_a = sum_{f=(a,b)} C_ab psi_b;  H_pin = 24 I - A.
  Trivial control: 24 - A_0 on the same graph (A_0 = panel-count adjacency), i.e. H = (24 - A_0) (x) I_2.  It is
  computed as the real n x n matrix 24 - A_0 and every eigenvalue is counted twice (exact spin degeneracy).
  Random admissible decoration: phase5a_controls.random_decorations(seed=20261021)[0], re-generated here with the
  same code and seed, verified to tile (check_tiling at levels 1, 2) and to give SO(3,Z) frames and Q8 links.
  Ideal Dirichlet cube (analytic): 6 - A on the L^3 cube of Z^3 with hard walls, eigenvalues
  6 - 2 sum_i cos(pi m_i/(L+1)), m_i = 1..L, spin-doubled; bulk edge E0 = 0 exactly; its IDS exponent is exactly 3/2
  in the infinite volume, so it shows what 3/2 looks like at these box sizes.

COUNTING CONVENTION.  Eigenvalues lambda_1 <= lambda_2 <= ... are counted with multiplicity (each Kramers pair
  contributes 2).  N(E) = #{i : lambda_i <= E} (right-continuous).  For a window k in [k1, k2] the points
  (x, y) = (log(lambda - E0), log N(lambda)) at the DISTINCT eigenvalues lambda in the window (lambda > E0) are fitted
  by least squares y = alpha x + c; the 'two-point' exponent is log(N(lambda_k2)/N(lambda_k1)) /
  log((lambda_k2 - E0)/(lambda_k1 - E0)).  A bootstrap-style spread is the 16-84 percentile range of alpha over
  random contiguous sub-windows [k1, k2] with 8 <= k1, k2 <= K, k2 >= 2 k1, >= 8 distinct eigenvalues.
  E0 conventions: (a) the extrapolated bulk edge (FR30: 8.76; trivial and cube: 0 exactly; random decoration:
  geometric extrapolation of the level-3,4,5 bottoms), (b) E0 = lambda_1 of the same level.
  Dirichlet-collapse test (H4/H5): if the patch spectrum near the edge is that of a homogenized effective-mass
  operator with hard walls, lambda_k(L+1) - E0 = (lambda_k(L) - E0)/4 (1 + O(1/2^L)) for fixed k << n; the ratios
  r_k(E0) = (lambda_k(5) - E0)/(lambda_k(4) - E0), k <= 200, are reported for the stated E0 and the E0 that
  minimizes the spread of log r_k (an independent estimate of the edge).

SOLVERS.  Level <= 4: dense LAPACK eigvalsh of the full matrix (8192 x 8192 complex at level 4).  Level 5 (dim 65536):
  Chebyshev-filtered subspace iteration (Zhou-Saad scaled filter on [theta_m, b], b a certified upper bound of the
  spectrum from Lanczos theta_max + residual) with block m = K + 40 on the exact sparse operator, Rayleigh-Ritz each
  pass, followed by matrix-free LOBPCG (scipy, diagonal preconditioner, seed 0) started from the lowest K + 4 Ritz
  vectors; eigenvalues are the Rayleigh quotients of the final normalized vectors and the residual norms
  ||H psi - lambda psi||_2 are computed with the exact sparse operator for every reported eigenpair (for a Hermitian
  operator |lambda_exact - lambda| <= residual).  The same pipeline is validated against the dense spectrum at level 4
  ('--pipeline-check').  Missed-eigenvalue checks: Kramers pairing of all reported eigenvalues, and agreement of the
  lowest 8 with the independent LOBPCG(block 8) run of phase5_bulk_bottom_lobpcg.py / phase5a_controls.py.

Run from the repository root (each 'compute' is one process, <= 3.5 GB, <= 40 min):
  python3 -u -I audit/phase5a_ids_edge.py compute --model fr30    --level 4 --K 400 --pipeline-check
  python3 -u -I audit/phase5a_ids_edge.py compute --model trivial --level 4 --K 400
  python3 -u -I audit/phase5a_ids_edge.py compute --model randdec --level 4 --K 400
  python3 -u -I audit/phase5a_ids_edge.py compute --model {fr30,randdec,trivial} --level 3 --K 400
  python3 -u -I audit/phase5a_ids_edge.py compute --model {fr30,randdec,trivial} --level 5 --K 200
  python3 -u -I audit/phase5a_ids_edge.py fit
Outputs: audit/results/phase5a_ids_edge_level{4,5}.npy (FR30 lowest K), phase5a_ids_edge_{trivial,randdec0}_level{L}.npy,
  phase5a_ids_edge_{model}_level{L}.json (metadata, residuals), phase5a_ids_edge_level4_full.npy (full level-4 FR30
  spectrum), phase5a_ids_edge.txt / phase5a_ids_edge_fit.json (the analysis).
"""
import os, sys, time, json, argparse, resource, warnings, itertools, collections
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
RES = os.path.join(HERE, 'results')
import numpy as np, scipy.sparse as sps, scipy.sparse.linalg as spl, scipy.linalg as sla
from independent_clifford_q8_audit import (FR30, U3, perm_mat, tiles_at_level, panel_edges, clifford_link, q8label,
                                           check_tiling, SIG)

Q8_NAMES = ['+1', '-1', '+i', '-i', '+j', '-j', '+k', '-k']
Q8_MATS = {'+1': np.eye(2, dtype=complex), '-1': -np.eye(2, dtype=complex)}
for _k, _nm in enumerate('ijk'):
    Q8_MATS['+' + _nm] = 1j * SIG[_k]; Q8_MATS['-' + _nm] = -1j * SIG[_k]
DEC_SEED = 20261021
E0_FR30 = 8.76

def maxrss_gb(): return resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 1e6
class Log:
    def __init__(self, path): self.fh = open(path, 'w')
    def __call__(self, msg=''):
        print(msg, flush=True); self.fh.write(msg + '\n'); self.fh.flush()
def conv(o):
    if isinstance(o, np.integer): return int(o)
    if isinstance(o, np.floating): return float(o)
    if isinstance(o, np.ndarray): return o.tolist()
    if isinstance(o, (frozenset, set, tuple)): return list(o)
    raise TypeError(str(type(o)))

# ---------------------------------------------------------------------------------------------------- decorations
PERMS = list(itertools.permutations(range(3)))
def sgn(p): return int(round(np.linalg.det(perm_mat(p))))
EVEN = [p for p in PERMS if sgn(p) == 1]; ODD = [p for p in PERMS if sgn(p) == -1]
def random_decorations(seed=DEC_SEED, count=6):
    """Verbatim re-implementation of phase5a_controls.random_decorations (same rng, same draw order)."""
    rng = np.random.default_rng(seed); decs = []
    while len(decs) < count:
        d = {'0': EVEN[rng.integers(3)]}
        for v in U3: d[v] = (EVEN if sum(v) % 2 == 0 else ODD)[rng.integers(3)]
        if d != FR30: decs.append(d)
    return decs
def frames_for(model):
    if model in ('fr30', 'trivial'): return FR30, None
    d = random_decorations()[0]
    for lvl in (1, 2):
        ov, exact, nc, nt = check_tiling(tiles_at_level(d, lvl), lvl)
        assert ov == 0 and exact, 'random decoration does not tile'
    return d, {str(k): list(v) for k, v in d.items()}

# ---------------------------------------------------------------------------------------------------- patch / operators
def build_patch(frames, level, log):
    t0 = time.time()
    tiles = tiles_at_level(frames, level); owner, edges = panel_edges(tiles); n = len(tiles); E = len(edges)
    ea = np.fromiter((e[0] for e in edges), np.int64, E); eb = np.fromiter((e[1] for e in edges), np.int64, E)
    eax = np.fromiter((int(np.argmax(e[2])) for e in edges), np.int64, E)
    Gall = np.array([G for G, _, _ in tiles], dtype=np.int64)
    for G in Gall[:: max(1, n // 64)]:
        assert (G.T @ G == np.eye(3, dtype=np.int64)).all() and round(np.linalg.det(G)) == 1, 'frame not in SO(3,Z)'
    keys, fid = np.unique(Gall.reshape(n, 9), axis=0, return_inverse=True); fid = np.asarray(fid).reshape(-1)
    framelist = [k.reshape(3, 3) for k in keys]; F = len(framelist)
    table = np.empty((F, F, 3), dtype=np.int64)
    for i in range(F):
        for j in range(F):
            for ax in range(3):
                nf = np.zeros(3, dtype=np.int64); nf[ax] = 1
                name = q8label(clifford_link(framelist[i], framelist[j], nf)); assert name != 'other', 'link not in Q8'
                table[i, j, ax] = Q8_NAMES.index(name)
    lab = table[fid[ea], fid[eb], eax]
    rng = np.random.default_rng(0)                      # direct per-edge cross-check of the table on a sample
    for idx in rng.choice(E, min(E, 3000), replace=False):
        C = clifford_link(tiles[ea[idx]][0], tiles[eb[idx]][0], edges[idx][2])
        assert np.allclose(C, Q8_MATS[Q8_NAMES[lab[idx]]]), 'link table mismatch'
    deg = np.bincount(ea, minlength=n) + np.bincount(eb, minlength=n)
    assert deg.max() == 24, 'bulk coordination is not 24'
    counts = dict(collections.Counter(Q8_NAMES[i] for i in lab.tolist()))
    log(f"patch level {level}: n={n} tiles, panels={E}, frames={F}, boundary tiles={(deg < 24).sum()}, link labels {counts}, "
        f"build {time.time()-t0:.1f}s rss={maxrss_gb():.2f}GB")
    return dict(n=n, E=E, ea=ea, eb=eb, lab=lab, deg=deg, label_counts=counts, n_boundary=int((deg < 24).sum()))

def H_clifford(P, diag=24.0):
    n, E = P['n'], P['E']
    rows = [np.arange(2 * n)]; cols = [np.arange(2 * n)]; vals = [np.full(2 * n, diag, dtype=complex)]
    for li, name in enumerate(Q8_NAMES):
        sel = np.nonzero(P['lab'] == li)[0]
        if len(sel) == 0: continue
        C = Q8_MATS[name]; a = P['ea'][sel]; b = P['eb'][sel]
        for r in range(2):
            for c in range(2):
                if C[r, c] != 0:
                    rows.append(2 * a + r); cols.append(2 * b + c); vals.append(np.full(len(sel), -C[r, c]))
                    rows.append(2 * b + c); cols.append(2 * a + r); vals.append(np.full(len(sel), -np.conj(C[r, c])))
    H = sps.csr_matrix((np.concatenate(vals), (np.concatenate(rows), np.concatenate(cols))), shape=(2 * n, 2 * n))
    H.sum_duplicates(); H.sort_indices(); return H
def H_tile(P, diag=24.0):
    n = P['n']
    rows = np.concatenate([np.arange(n), P['ea'], P['eb']]); cols = np.concatenate([np.arange(n), P['eb'], P['ea']])
    vals = np.concatenate([np.full(n, diag), -np.ones(P['E']), -np.ones(P['E'])])
    H = sps.csr_matrix((vals, (rows, cols)), shape=(n, n)); H.sum_duplicates(); H.sort_indices(); return H

# ---------------------------------------------------------------------------------------------------- solvers
def dense_all(H):
    return sla.eigvalsh(H.toarray(), overwrite_a=True, check_finite=False)

def spectrum_upper_bound(H):
    """Certified upper bound of spec(H): Lanczos Ritz value theta_max plus its residual norm (Hermitian H)."""
    w, V = spl.eigsh(H, k=1, which='LA', tol=1e-8, maxiter=5000)
    v = V[:, 0] / np.linalg.norm(V[:, 0]); r = np.linalg.norm(H @ v - w[0] * v)
    return float(w[0]), float(r), float(w[0] + r)

def residuals(H, X, th, chunk=16):
    r = np.empty(len(th))
    for j in range(0, len(th), chunk):
        Xj = X[:, j:j + chunk]; r[j:j + chunk] = np.linalg.norm(H @ Xj - Xj * th[None, j:j + chunk], axis=0)
    return r

def rayleigh_ritz(H, Y):
    Q, _ = np.linalg.qr(Y, mode='reduced'); del Y
    HQ = H @ Q; G = Q.conj().T @ HQ; G = 0.5 * (G + G.conj().T)
    th, U = np.linalg.eigh(G); X = Q @ U; del Q
    HX = HQ @ U; del HQ
    res = np.linalg.norm(HX - X * th[None, :], axis=0); del HX
    return X, th, res

def chebfsi(H, K, m, b, tol, log, max_passes=60, time_budget=1500.0, deg0=30, deg_max=80, seed=0, dtype=complex):
    """Chebyshev-filtered subspace iteration for the lowest K eigenpairs (block m >= K), Zhou-Saad scaled filter on
    [a, b] with a = largest current Ritz value, b >= lambda_max.  Returns X (N x m), Ritz values, exact residuals."""
    N = H.shape[0]; rng = np.random.default_rng(seed)
    X = rng.standard_normal((N, m)).astype(dtype)
    if dtype == complex: X += 1j * rng.standard_normal((N, m))
    t0 = time.time(); nmv = 0
    X, th, res = rayleigh_ritz(H, X); nmv += 1
    lam_min_est = float(th[0]); deg = deg0; hist = []
    for p in range(max_passes):
        a = float(th[-1]); e = (b - a) / 2.0; c = (b + a) / 2.0
        a0 = lam_min_est - 0.05 * (a - lam_min_est) - 1e-3
        sigma = e / (a0 - c); sigma1 = sigma
        Y = H @ X; Y -= c * X; Y *= (sigma1 / e); nmv += 1
        for i in range(2, deg + 1):
            sigma_new = 1.0 / (2.0 / sigma1 - sigma)
            Z = H @ Y; Z -= c * Y; Z *= (2.0 * sigma_new / e); Z -= (sigma * sigma_new) * X; nmv += 1
            X = Y; Y = Z; del Z; sigma = sigma_new
        del X
        X, th, res = rayleigh_ritz(H, Y); nmv += 1
        lam_min_est = min(lam_min_est, float(th[0]))
        worst = float(res[:K].max())
        hist.append(dict(pass_=p, deg=deg, theta_1=float(th[0]), theta_K=float(th[K - 1]), theta_m=float(th[-1]), resK_max=worst,
                         resK_median=float(np.median(res[:K])), matvecs=nmv, time_s=time.time() - t0))
        log(f"   cheb pass {p:2d} deg {deg:3d} nmv {nmv:5d}  theta_1={th[0]:.8f} theta_K={th[K-1]:.8f} theta_m={th[-1]:.6f}  "
            f"res[:K] max={worst:.1e} median={np.median(res[:K]):.1e}  {time.time()-t0:.0f}s rss={maxrss_gb():.2f}GB")
        if worst < tol: break
        if time.time() - t0 > time_budget: log("   chebfsi time budget exhausted"); break
        deg = min(deg_max, deg + 10)
    return X, th, res, hist

def lobpcg_polish(H, X0, K, tol, maxiter, log, dtype=complex):
    """scipy LOBPCG with diagonal preconditioner, started from X0 (N x (K+guard)); returns lowest K Rayleigh quotients,
    vectors and exact residuals."""
    N = H.shape[0]; dinv = 1.0 / H.diagonal().real
    M = spl.LinearOperator(H.shape, matvec=lambda v: dinv * v, matmat=lambda B: dinv[:, None] * B, dtype=dtype)
    t0 = time.time(); msgs = []
    with warnings.catch_warnings(record=True) as wl:
        warnings.simplefilter('always'); w, V = spl.lobpcg(H, X0, M=M, largest=False, tol=tol, maxiter=maxiter)
        msgs = [str(x.message)[:160].replace('\n', ' ') for x in wl]
    o = np.argsort(w.real); V = V[:, o]; V /= np.linalg.norm(V, axis=0)
    HV = H @ V; lam = np.real(np.einsum('ij,ij->j', V.conj(), HV)); res = np.linalg.norm(HV - V * lam[None, :], axis=0); del HV
    o = np.argsort(lam); lam, V, res = lam[o], V[:, o], res[o]
    log(f"   lobpcg polish: block {X0.shape[1]}, {time.time()-t0:.0f}s, warnings: {msgs if msgs else 'none'}; res[:K] max={res[:K].max():.1e} median={np.median(res[:K]):.1e}")
    return lam[:K], V[:, :K], res[:K]

def lobpcg_lowest8(H, seed=0, dtype=complex):
    """Independent check of the lowest 8: LOBPCG block 10 from a random start (as in phase5a_controls.py)."""
    N = H.shape[0]; rng = np.random.default_rng(seed)
    X = rng.standard_normal((N, 10)).astype(dtype)
    if dtype == complex: X += 1j * rng.standard_normal((N, 10))
    dinv = 1.0 / H.diagonal().real
    M = spl.LinearOperator(H.shape, matvec=lambda v: dinv * v, matmat=lambda B: dinv[:, None] * B, dtype=dtype)
    with warnings.catch_warnings():
        warnings.simplefilter('ignore'); w, V = spl.lobpcg(H, X, M=M, largest=False, tol=1e-7, maxiter=6000)
    o = np.argsort(w.real)[:8]; V = V[:, o]; V /= np.linalg.norm(V, axis=0)
    HV = H @ V; lam = np.real(np.einsum('ij,ij->j', V.conj(), HV)); res = np.linalg.norm(HV - V * lam[None, :], axis=0)
    return lam, res

# ---------------------------------------------------------------------------------------------------- compute
def tag(model): return {'fr30': '', 'trivial': 'trivial_', 'randdec': 'randdec0_'}[model]
def compute(args):
    model, level, K = args.model, args.level, args.K
    log = Log(os.path.join(RES, f'phase5a_ids_edge_{tag(model)}level{level}.log'))
    log(f"=== phase5a_ids_edge compute: model={model} level={level} K={K} (threads OMP={os.environ.get('OMP_NUM_THREADS')}) ===")
    frames, dec = frames_for(model)
    if dec: log(f"random admissible decoration #0 (rng seed {DEC_SEED}): {dec}")
    P = build_patch(frames, level, log)
    rec = dict(model=model, level=level, n=P['n'], panels=P['E'], n_boundary=P['n_boundary'], label_counts=P['label_counts'],
               decoration=dec, K=K, convention=('H = (24 - A_0) (x) I_2 computed as the real n x n matrix 24 - A_0, each eigenvalue counted twice'
                                                 if model == 'trivial' else 'H_pin = 24 I - A on l^2(tiles) x C^2, Clifford Q8 links'))
    t0 = time.time()
    if model == 'trivial':
        H = H_tile(P); dtype = float
    else:
        H = H_clifford(P); dtype = complex
    assert abs(H - H.getH()).max() < 1e-12
    rec['dim'] = int(H.shape[0]); rec['nnz'] = int(H.nnz); log(f"operator dim {H.shape[0]} nnz {H.nnz} hermitian; build {time.time()-t0:.1f}s")
    Kd = K // 2 if model == 'trivial' else K                       # distinct (tile) eigenvalues needed for the trivial model
    if level <= 4:
        t0 = time.time(); w = dense_all(H); dt = time.time() - t0
        log(f"dense eigvalsh dim {H.shape[0]}: {dt:.0f}s rss={maxrss_gb():.2f}GB; lambda_min={w[0]:.9f} lambda_max={w[-1]:.6f} mean={w.mean():.6f} (trace/dim = {H.diagonal().real.mean():.3f})")
        lam_full = np.repeat(w, 2) if model == 'trivial' else w
        lam = lam_full[:K]; res = np.zeros(K)
        rec.update(solver=f'dense eigvalsh (LAPACK), dim {H.shape[0]}', seconds=dt, lambda_max=float(w[-1]), spectral_mean=float(w.mean()),
                   residual_note='dense LAPACK eigenvalues: backward error ~ eps * ||H|| ~ 1e-14; no per-pair residual')
        np.save(os.path.join(RES, f'phase5a_ids_edge_{tag(model)}level{level}_full.npy'), lam_full)
        if model == 'fr30' and level == 4:
            p = os.path.join(RES, 'level4_clifford_pinned_eigs.npy')
            if os.path.exists(p):
                ref = np.load(p); rec['max_diff_vs_phase5_dense'] = float(np.abs(ref - w).max())
                log(f"check vs phase-5 saved dense level-4 pinned spectrum (audit/results/level4_clifford_pinned_eigs.npy): max|diff| = {rec['max_diff_vs_phase5_dense']:.2e}")
        if args.pipeline_check and model != 'trivial':
            log("--- pipeline check at level 4: Chebyshev FSI (block K+40) + LOBPCG polish vs dense, K=200 ---")
            thm, rmax, b = spectrum_upper_bound(H); log(f"   Lanczos theta_max={thm:.6f} residual {rmax:.1e} -> b={b:.6f} (dense lambda_max {w[-1]:.6f})")
            X, th, rs, hist = chebfsi(H, 200, 240, b, 1e-7, log, time_budget=600.0)
            lam2, V2, res2 = lobpcg_polish(H, X[:, :204], 200, 1e-8, 50, log); del X
            rec['pipeline_check'] = dict(cheb_passes=len(hist), cheb_resK_max=float(rs[:200].max()), final_resK_max=float(res2.max()),
                                         max_abs_diff_vs_dense_K200=float(np.abs(lam2 - w[:200]).max()), cheb_only_max_abs_diff=float(np.abs(th[:200] - w[:200]).max()))
            log(f"   pipeline vs dense (lowest 200): max|diff| = {rec['pipeline_check']['max_abs_diff_vs_dense_K200']:.2e} (Chebyshev-only {rec['pipeline_check']['cheb_only_max_abs_diff']:.2e}); final max residual {res2.max():.1e}")
    else:
        thm, rmax, b = spectrum_upper_bound(H); log(f"Lanczos theta_max={thm:.6f} residual {rmax:.1e} -> certified upper bound b={b:.6f}")
        rec['lambda_max_lanczos'] = thm; rec['upper_bound_b'] = b
        m = Kd + 40; t0 = time.time()
        X, th, rs, hist = chebfsi(H, Kd, m, b, args.cheb_tol, log, time_budget=args.cheb_budget, dtype=dtype)
        rec['chebyshev'] = dict(block=m, passes=len(hist), history=hist, resK_max=float(rs[:Kd].max()), seconds=time.time() - t0)
        th_cheb = th[:Kd].copy(); X0 = np.ascontiguousarray(X[:, :Kd + 4]); del X
        t1 = time.time()
        lam_d, V, res_d = lobpcg_polish(H, X0, Kd, args.lobpcg_tol, args.lobpcg_maxiter, log, dtype=dtype); del X0
        rec['lobpcg'] = dict(block=Kd + 4, tol=args.lobpcg_tol, maxiter=args.lobpcg_maxiter, seconds=time.time() - t1,
                             max_shift_vs_chebyshev=float(np.abs(lam_d - th_cheb).max()))
        log(f"   LOBPCG polish moved the Ritz values by at most {rec['lobpcg']['max_shift_vs_chebyshev']:.1e}; total solve {time.time()-t0:.0f}s rss={maxrss_gb():.2f}GB")
        if model == 'trivial':
            lam = np.repeat(lam_d, 2)[:K]; res = np.repeat(res_d, 2)[:K]
        else:
            lam, res = lam_d[:K], res_d[:K]
        rec.update(solver=f'Chebyshev FSI (block {m}) + LOBPCG (block {Kd+4}, diag precond, seed 0)', seconds=time.time() - t0,
                   residual_note='||H psi - lambda psi||_2 with the exact sparse operator, lambda = <psi|H|psi>, ||psi||=1')
        # independent check of the lowest 8 by LOBPCG(block 10) from a random start
        t2 = time.time(); l8, r8 = lobpcg_lowest8(H, dtype=dtype)
        l8c = np.repeat(l8, 2)[:8] if model == 'trivial' else l8
        rec['lowest8_lobpcg_random_start'] = dict(eigenvalues=l8c.tolist(), residuals=r8.tolist(), max_abs_diff=float(np.abs(l8c - lam[:8]).max()), seconds=time.time() - t2)
        log(f"   independent LOBPCG(block 10, random start) lowest 8: {np.array2string(l8c, precision=7, max_line_width=200)}; max|diff| vs pipeline = {rec['lowest8_lobpcg_random_start']['max_abs_diff']:.1e} (res max {r8.max():.1e}, {time.time()-t2:.0f}s)")
    if model != 'trivial':
        rec['kramers_max_split'] = float(np.abs(lam[1::2] - lam[0::2]).max())
        log(f"Kramers pairing of the {K} reported eigenvalues: max|lambda_(2j) - lambda_(2j-1)| = {rec['kramers_max_split']:.1e}")
    rec['eigenvalues'] = lam.tolist(); rec['residuals'] = res.tolist()
    rec['max_residual'] = float(res.max()); rec['maxrss_gb'] = maxrss_gb()
    np.save(os.path.join(RES, f'phase5a_ids_edge_{tag(model)}level{level}.npy'), lam)
    with open(os.path.join(RES, f'phase5a_ids_edge_{tag(model)}level{level}.json'), 'w') as f: json.dump(rec, f, indent=1, default=conv)
    log(f"lowest 12: {np.array2string(lam[:12], precision=7, max_line_width=220)}")
    log(f"lambda_k at k = 8, 32, 128, {K}: {lam[7]:.7f} {lam[31]:.7f} {lam[min(127, K-1)]:.7f} {lam[K-1]:.7f}; max residual {res.max():.1e}")
    log(f"saved audit/results/phase5a_ids_edge_{tag(model)}level{level}.npy/.json  (rss {maxrss_gb():.2f} GB)")

# ---------------------------------------------------------------------------------------------------- analysis
def cube_spectrum(L, K):
    m = np.arange(1, L + 1); e = 2 - 2 * np.cos(np.pi * m / (L + 1))
    mu = np.sort((e[:, None, None] + e[None, :, None] + e[None, None, :]).ravel())
    return np.repeat(mu, 2)[:K]

def window_points(lam, E0, k1, k2):
    lam = np.asarray(lam); k = np.arange(1, len(lam) + 1)
    sel = (k >= k1) & (k <= k2) & (lam - E0 > 0)
    vals = np.unique(lam[sel])
    N = np.searchsorted(lam, vals, side='right')          # right-continuous count over the whole list
    return np.log(vals - E0), np.log(N.astype(float))
def fit_window(lam, E0, k1, k2):
    x, y = window_points(lam, E0, k1, k2)
    if len(x) < 3: return dict(k1=k1, k2=k2, npts=int(len(x)), alpha=None, stderr=None, alpha_2pt=None)
    A = np.vstack([x, np.ones_like(x)]).T; coef, resid, *_ = np.linalg.lstsq(A, y, rcond=None)
    r = y - A @ coef; s2 = (r @ r) / max(1, len(x) - 2); cov = s2 * np.linalg.inv(A.T @ A)
    k1e = max(k1, int(np.searchsorted(lam, E0, side='right')) + 1)
    N1, N2 = np.searchsorted(lam, lam[k1e - 1], side='right'), np.searchsorted(lam, lam[k2 - 1], side='right')
    a2 = float(np.log(N2 / N1) / np.log((lam[k2 - 1] - E0) / (lam[k1e - 1] - E0)))
    return dict(k1=k1, k2=k2, npts=int(len(x)), alpha=float(coef[0]), stderr=float(np.sqrt(cov[0, 0])), alpha_2pt=a2, rms_log_resid=float(np.sqrt(np.mean(r**2))))
def bootstrap_windows(lam, E0, K, nboot=3000, seed=1):
    rng = np.random.default_rng(seed); out = []
    for _ in range(nboot):
        k1 = int(rng.integers(8, K // 2 + 1)); k2 = int(rng.integers(2 * k1, K + 1)) if 2 * k1 <= K else K
        f = fit_window(lam, E0, k1, k2)
        if f['alpha'] is not None and f['npts'] >= 8: out.append(f['alpha'])
    a = np.array(out)
    return dict(n=len(a), median=float(np.median(a)), p16=float(np.percentile(a, 16)), p84=float(np.percentile(a, 84)), min=float(a.min()), max=float(a.max())) if len(a) else None
def weyl_fits(lam, E0, k1, k2):
    """Two 2-parameter fits of N(E) over the window at the distinct eigenvalues: pure power N = C (E-E0)^alpha (log-log LS,
    as fit_window) and the Dirichlet two-term Weyl form N = a (E-E0)^(3/2) + b (E-E0) (linear LS); relative rms misfits."""
    lam = np.asarray(lam); k = np.arange(1, len(lam) + 1); sel = (k >= k1) & (k <= k2) & (lam - E0 > 0)
    vals = np.unique(lam[sel]); N = np.searchsorted(lam, vals, side='right').astype(float); x = vals - E0
    if len(x) < 4: return None
    # all three fits minimize the RELATIVE residual (rows divided by N), so the misfits are comparable
    A = np.vstack([x**1.5, x]).T; c, *_ = np.linalg.lstsq(A / N[:, None], np.ones_like(N), rcond=None); rel_w = float(np.sqrt(np.mean(((A @ c - N) / N)**2)))
    B = np.vstack([np.log(x), np.ones_like(x)]).T; d, *_ = np.linalg.lstsq(B, np.log(N), rcond=None); rel_p = float(np.sqrt(np.mean((np.exp(B @ d) / N - 1)**2)))
    A1 = x[:, None]**1.5; c1, *_ = np.linalg.lstsq(A1 / N[:, None], np.ones_like(N), rcond=None); rel_1 = float(np.sqrt(np.mean(((A1 @ c1).ravel() - N) / N)**2))
    return dict(weyl_a=float(c[0]), weyl_b=float(c[1]), weyl_rel_rms=rel_w, power_alpha=float(d[0]), power_rel_rms=rel_p, pure32_rel_rms=rel_1,
                surface_over_volume_at_kmax=float(c[1] * x[-1] / (c[0] * x[-1]**1.5)))

def collapse(l4, l5, E0grid, E0_stated, kmax=200):
    k = min(kmax, len(l4), len(l5)); a4 = np.asarray(l4[:k]); a5 = np.asarray(l5[:k])
    def spread(E0):
        r = (a5 - E0) / (a4 - E0)
        if np.any(a5 - E0 <= 0): return np.inf, r
        return float(np.std(np.log(r))), r
    best = min(E0grid, key=lambda e: spread(e)[0]); sb, rb = spread(best); ss, rs = spread(E0_stated)
    def summ(r): return dict(median=float(np.median(r)), p16=float(np.percentile(r, 16)), p84=float(np.percentile(r, 84)), r1=float(r[0]), r8=float(r[7]), r_last=float(r[-1]), std_log=float(np.std(np.log(r))))
    return dict(k=k, E0_stated=E0_stated, ratios_stated=summ(rs), E0_best=float(best), ratios_best=summ(rb), spread_best=sb,
                grid=[float(E0grid[0]), float(E0grid[-1])])

def load(model, level):
    p = os.path.join(RES, f'phase5a_ids_edge_{tag(model)}level{level}.npy'); j = os.path.join(RES, f'phase5a_ids_edge_{tag(model)}level{level}.json')
    if not os.path.exists(p): return None, None
    return np.load(p), (json.load(open(j)) if os.path.exists(j) else {})

def fit(args):
    log = Log(os.path.join(RES, 'phase5a_ids_edge.txt')); out = dict(windows=[[8, 32], [32, 128], [128, 'K'], [8, 'K']], models={})
    log("PHASE 5a / TASK B4: integrated density of states near the edge of the pinned FR30 operator, with controls")
    log("=" * 128)
    log(__doc__.split('COUNTING CONVENTION.')[1].split('SOLVERS.')[0].strip())
    log("")
    data = {}
    for model in ('fr30', 'trivial', 'randdec'):
        for level in (3, 4, 5):
            lam, meta = load(model, level)
            if lam is not None: data[(model, level)] = (lam, meta)
    for L in (4, 5):
        data[('cube', L)] = (cube_spectrum(2**L, 400 if L == 4 else 200), dict(solver='exact formula', residuals=[0.0], n=8**L, K=400 if L == 4 else 200))
    # bulk-edge estimates
    E0 = {'fr30': E0_FR30, 'trivial': 0.0, 'cube': 0.0}
    bots = {lv: data[('randdec', lv)][0][0] for lv in (3, 4, 5) if ('randdec', lv) in data}
    if len(bots) == 3:
        d1, d2 = bots[3] - bots[4], bots[4] - bots[5]; r = d2 / d1; E0['randdec'] = float(bots[5] - d2 * r / (1 - r))
        out['randdec_edge'] = dict(bottoms=bots, decrements=[d1, d2], ratio=r, E0_geometric=E0['randdec'], upper_bound=bots[5])
        log(f"random decoration #0 bottoms: L3 {bots[3]:.6f} L4 {bots[4]:.6f} L5 {bots[5]:.6f}; decrements {d1:.5f}, {d2:.5f} (ratio {r:.3f}); geometric extrapolation E0 = {E0['randdec']:.4f} (rigorous: E0 <= {bots[5]:.5f})")
    elif ('randdec', 5) in data: E0['randdec'] = float(data[('randdec', 5)][0][0]) - 0.03
    fb = {lv: data[('fr30', lv)][0][0] for lv in (3, 4, 5) if ('fr30', lv) in data}
    if len(fb) == 3:
        d1, d2 = fb[3] - fb[4], fb[4] - fb[5]; r = d2 / d1
        out['fr30_edge'] = dict(bottoms=fb, decrements=[d1, d2], ratio=r, E0_geometric=float(fb[5] - d2 * r / (1 - r)), E0_used=E0_FR30, level6_upper_bound=8.77013)
        log(f"FR30 bottoms: L3 {fb[3]:.6f} L4 {fb[4]:.6f} L5 {fb[5]:.6f}; decrements {d1:.5f}, {d2:.5f} (ratio {r:.3f}); geometric extrapolation {out['fr30_edge']['E0_geometric']:.4f}; level-6 value 8.77013 (phase 5); E0 used = {E0_FR30}")
    log("")
    names = {'fr30': 'FR30 Clifford Q8, pinned (H_pin = 24 - A)', 'trivial': 'trivial connection on the FR30 graph, pinned (24 - A_0)',
             'randdec': 'random admissible decoration #0, Clifford links, pinned', 'cube': 'ideal Dirichlet cube L^3 (6 - A on Z^3 box), exact, alpha_bulk = 3/2'}
    for model in ('fr30', 'trivial', 'randdec', 'cube'):
        for level in (4, 5):
            if (model, level) not in data: continue
            lam, meta = data[(model, level)]; K = len(lam); n = 8**level
            e0b = E0.get(model); l1 = float(lam[0])
            log("-" * 128); log(f"{names[model]} | level {level} (n = {n} tiles), K = {K} lowest eigenvalues; solver: {meta.get('solver')}; max residual {max(meta.get('residuals', [0.0])):.1e}")
            log(f"   lambda_1 = {l1:.7f}; lambda_8 = {lam[7]:.7f}; lambda_32 = {lam[31]:.7f}; lambda_128 = {lam[min(127, K-1)]:.7f}; lambda_K = {lam[K-1]:.7f}")
            rec = dict(K=K, n=n, lambda_1=l1, E0_bulk=e0b, fits={})
            for e0name, e0 in (('E0_bulk', e0b), ('E0_lambda1', l1)):
                if e0 is None: continue
                rows = []
                for (k1, k2) in ((8, 32), (32, 128), (128, K), (8, K)):
                    if k2 <= k1 or k2 > K: continue
                    rows.append(fit_window(lam, e0, k1, k2))
                bs = bootstrap_windows(lam, e0, K); wf = weyl_fits(lam, e0, 8, K)
                rec['fits'][e0name] = dict(E0=e0, windows=rows, bootstrap=bs, weyl=wf)
                lab = f"E0 = {e0:.5f} ({'extrapolated bulk edge' if e0name == 'E0_bulk' else 'lambda_1 of this level'})"
                log(f"   {lab}:")
                for f in rows:
                    if f['alpha'] is None: log(f"      k in [{f['k1']},{f['k2']}]: too few points"); continue
                    log(f"      k in [{f['k1']:3d},{f['k2']:3d}] ({f['npts']:3d} distinct eigenvalues): alpha_LS = {f['alpha']:.3f} +- {f['stderr']:.3f} (nominal), alpha_2pt = {f['alpha_2pt']:.3f}, rms log-resid {f['rms_log_resid']:.3f}")
                if bs: log(f"      bootstrap over {bs['n']} random sub-windows: alpha median {bs['median']:.3f}, 16-84% [{bs['p16']:.3f}, {bs['p84']:.3f}], range [{bs['min']:.3f}, {bs['max']:.3f}]")
                if wf: log(f"      k in [8,{K}] fits of N(E): power law alpha={wf['power_alpha']:.3f} rel.rms {wf['power_rel_rms']:.3f}; pure C(E-E0)^1.5 rel.rms {wf['pure32_rel_rms']:.3f}; "
                           f"Weyl two-term a(E-E0)^1.5 + b(E-E0): a={wf['weyl_a']:.3f} b={wf['weyl_b']:+.3f} rel.rms {wf['weyl_rel_rms']:.3f} (|surface/volume| term at k=K: {wf['surface_over_volume_at_kmax']:+.3f})")
            out['models'][f'{model}_L{level}'] = rec
    # Dirichlet collapse between levels 4 and 5
    log("-" * 128); log("DIRICHLET-COLLAPSE TEST between levels 4 and 5: r_k(E0) = (lambda_k(5) - E0)/(lambda_k(4) - E0), k <= 200 (homogenized hard-wall box: r_k -> 1/4 for all k)")
    for model in ('fr30', 'trivial', 'randdec', 'cube'):
        if (model, 4) not in data or (model, 5) not in data or E0.get(model) is None: continue
        l4, l5 = data[(model, 4)][0], data[(model, 5)][0]; e0 = E0[model]
        grid = np.linspace(l5[0] - 0.6, l5[0] - 1e-4, 1201) if model != 'cube' else np.linspace(-0.3, l5[0] - 1e-4, 601)
        c = collapse(l4, l5, grid, e0); out.setdefault('collapse', {})[model] = c; rs, rb = c['ratios_stated'], c['ratios_best']
        log(f"   {model:8s} E0 stated {e0:.5f}: r_1={rs['r1']:.4f} r_8={rs['r8']:.4f} r_200={rs['r_last']:.4f}, median {rs['median']:.4f} [16-84%: {rs['p16']:.4f}, {rs['p84']:.4f}], std(log r)={rs['std_log']:.3f} | "
            f"best-collapse E0 = {c['E0_best']:.4f}: median r {rb['median']:.4f} [{rb['p16']:.4f}, {rb['p84']:.4f}], std(log r)={rb['std_log']:.3f}")
    # same-energy IDS ratio N_5(E)/N_4(E) (extensivity, independent of E0)
    log("-" * 128); log("SAME-ENERGY IDS RATIO N_5(E)/N_4(E) at E = lambda_k(5), k = 8, 32, 128, 200 (bulk-like states: -> 8 = volume ratio; a ratio below 8 means the level-4 count at that energy is relatively inflated or the edge has not converged)")
    for model in ('fr30', 'trivial', 'randdec', 'cube'):
        if (model, 4) not in data or (model, 5) not in data: continue
        l4, l5 = data[(model, 4)][0], data[(model, 5)][0]; row = {}
        for k in (8, 32, 128, 200):
            if k > len(l5): continue
            E = l5[k - 1]; N4 = int(np.searchsorted(l4, E, side='right')); N5 = int(np.searchsorted(l5, E, side='right'))
            row[k] = dict(E=float(E), N4=N4, N5=N5, ratio=(N5 / N4 if N4 > 0 else None))
        out.setdefault('same_energy', {})[model] = row
        log(f"   {model:8s} " + '  '.join(f"k={k}: E={v['E']:.5f} N4={v['N4']:3d} N5={v['N5']:3d} ratio={'%.2f' % v['ratio'] if v['ratio'] else 'inf(N4=0)'}" for k, v in row.items()))
    with open(os.path.join(RES, 'phase5a_ids_edge_fit.json'), 'w') as f: json.dump(out, f, indent=1, default=conv)
    log(""); log("saved audit/results/phase5a_ids_edge.txt and audit/results/phase5a_ids_edge_fit.json")

if __name__ == '__main__':
    ap = argparse.ArgumentParser(); sub = ap.add_subparsers(dest='cmd', required=True)
    c = sub.add_parser('compute'); c.add_argument('--model', choices=['fr30', 'trivial', 'randdec'], required=True)
    c.add_argument('--level', type=int, required=True); c.add_argument('--K', type=int, default=400)
    c.add_argument('--pipeline-check', action='store_true'); c.add_argument('--cheb-tol', type=float, default=1e-7)
    c.add_argument('--cheb-budget', type=float, default=1500.0); c.add_argument('--lobpcg-tol', type=float, default=1e-8)
    c.add_argument('--lobpcg-maxiter', type=int, default=60)
    sub.add_parser('fit')
    a = ap.parse_args()
    compute(a) if a.cmd == 'compute' else fit(a)
