#!/usr/bin/env python3
"""
Phase V-B / Workstream D: level-7 FR30 pinned ground state (n = 2097152 tiles, dim 4194304) by Chebyshev-filtered
subspace iteration with checkpoint/restart, and the exact rational certification of the resulting bottom.

Operator: H_pin = 24 I_2 - A on l^2(tiles) x C^2 (conventions of audit/phase5a_controls.py; spec(H) in [0, 48]).
Geometry: audit/phase5b_d_scaling.geometry (own vectorised builder, validated against the object builders at L3-5);
H assembled per axis (three CSR pieces summed) to keep the build peak low.
Solver: K = 4 wanted eigenpairs (two Kramers pairs), block m = 16, Zhou-Saad scaled Chebyshev filter on
[theta_m, 48] with degree ramp 40 -> 200, exact Rayleigh-Ritz (Cholesky-QR in place, H applied to the orthonormal
block) after every pass; stop when the lowest 4 residuals ||H psi - theta psi|| <= tol (1e-7).  Memory layout: at most
three N x m complex128 blocks alive (X, Y, Z / Q, HQ), ~3.2 GB at level 7, plus H (~0.8 GB).
Checkpoint after every pass (two generations ckpt_a/ckpt_b, atomic rename): X, theta, residuals, pass, block matvecs,
rng state, elapsed; --resume reloads the newest complete checkpoint.
Outputs (level 7): audit/results/phase5b_d_level7.log (one line per pass), phase5b_d_fr30_level7_lowest4.npy,
phase5b_d_fr30_level7_groundstate_weights.npy, phase5b_d_level7.json.  Levels < 7 (tests): same names with _L<level>.

Usage (repository root):
  OMP_NUM_THREADS=2 python3 -u -I audit/phase5b_d_level7.py run <level> [--resume] [--tol 1e-7] [--block 16] [--K 4]
  python3 -u -I audit/phase5b_d_level7.py certify <level>      # exact Rayleigh quotient of the saved lowest vector (numpy int64 chunked)
"""
import os, sys, time, json, resource, argparse
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
RES = os.path.join(HERE, 'results')
CKDIR = '/tmp/claude-0/-home-user--/3e28775d-be57-5932-b9d4-6e0f425b644f/scratchpad/phase5b/level7'
import numpy as np, scipy.sparse as sps, scipy.linalg as sla
import phase5b_d_scaling as D

def rss_gb(): return resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 1e6
def names(level):
    suf = '' if level == 7 else f'_L{level}'
    return dict(log=os.path.join(RES, f'phase5b_d_level7{suf}.log'), vec=os.path.join(RES, f'phase5b_d_fr30_level7{suf}_lowest4.npy'),
                w=os.path.join(RES, f'phase5b_d_fr30_level7{suf}_groundstate_weights.npy'), js=os.path.join(RES, f'phase5b_d_level7{suf}.json'),
                ck=[os.path.join(CKDIR, f'ckpt_{g}{suf}.npz') for g in 'ab'])

class Log:
    def __init__(self, path): self.fh = open(path, 'a')
    def __call__(self, msg):
        line = f"[{time.strftime('%Y-%m-%d %H:%M:%S')}] {msg}"; print(line, flush=True); self.fh.write(line + '\n'); self.fh.flush()

# ---------------------------------------------------------------- operator, assembled per axis
def build_H_per_axis(geo, log):
    n, ea, eb, eax, lab = geo['n'], geo['ea'], geo['eb'], geo['eax'], geo['lab']; N = 2 * n
    H = sps.diags(np.full(N, 24.0, dtype=complex), format='csr')
    for ax in range(3):
        sel_ax = np.nonzero(eax == ax)[0]; rows, cols, vals = [], [], []
        for li, name in enumerate(D.Q8_NAMES):
            sel = sel_ax[lab[sel_ax] == li]
            if len(sel) == 0: continue
            C = D.Q8_MATS[name]; a = ea[sel]; b = eb[sel]
            for r in range(2):
                for c in range(2):
                    if C[r, c] != 0:
                        rows.append((2 * a + r).astype(np.int32)); cols.append((2 * b + c).astype(np.int32)); vals.append(np.full(len(sel), -C[r, c]))
                        rows.append((2 * b + c).astype(np.int32)); cols.append((2 * a + r).astype(np.int32)); vals.append(np.full(len(sel), -np.conj(C[r, c])))
        piece = sps.csr_matrix((np.concatenate(vals), (np.concatenate(rows), np.concatenate(cols))), shape=(N, N)); del rows, cols, vals
        piece.sum_duplicates(); H = (H + piece).tocsr(); del piece
        log(f"   axis {ax}: {len(sel_ax)} panels assembled, running nnz {H.nnz}, rss {rss_gb():.2f} GB")
    H.sum_duplicates(); H.eliminate_zeros(); H.sort_indices()
    return H

# ---------------------------------------------------------------- in-place block helpers
CH = 1 << 17
def inplace_matmul(B, U):
    for j in range(0, B.shape[0], CH): B[j:j + CH] = B[j:j + CH] @ U
    return B
def chol_qr(Y):
    """Two passes of Cholesky-QR in place; returns orthogonality error."""
    for _ in range(2):
        G = Y.conj().T @ Y; Rf = np.linalg.cholesky(G).conj().T
        Rinv = sla.solve_triangular(Rf, np.eye(Rf.shape[0], dtype=Rf.dtype), check_finite=False); inplace_matmul(Y, Rinv)
    G = Y.conj().T @ Y; return float(np.abs(G - np.eye(G.shape[0])).max())
def rayleigh_ritz(H, Y):
    """Exact Rayleigh-Ritz on the block Y (consumed): returns X (= Y rotated), theta, residuals, orth error."""
    orth = chol_qr(Y); HQ = H @ Y
    G = Y.conj().T @ HQ; G = 0.5 * (G + G.conj().T); th, U = np.linalg.eigh(G)
    inplace_matmul(Y, U); inplace_matmul(HQ, U)
    res = np.empty(len(th))
    for j in range(len(th)): res[j] = np.linalg.norm(HQ[:, j] - th[j] * Y[:, j])
    del HQ; return Y, th, res, orth

def save_ckpt(paths, gen, X, th, res, p, nmv, rng, elapsed):
    path = paths[gen % 2]; tmp = path[:-4] + '_tmp.npz'          # np.savez keeps a name that already ends in .npz
    np.savez(tmp, X=X, theta=th, res=res, pass_=p, nmv=nmv, rng_state=json.dumps(rng.bit_generator.state), elapsed=elapsed)
    os.replace(tmp, path)
def load_newest(paths):
    cands = [p for p in paths if os.path.exists(p)]
    if not cands: return None
    return np.load(max(cands, key=os.path.getmtime), allow_pickle=False)

# ---------------------------------------------------------------- main run
def run(level, resume, tol, m, K, deg0=40, deg_max=200, max_passes=400):
    os.makedirs(CKDIR, exist_ok=True); nm = names(level); log = Log(nm['log']); T0 = time.time()
    log(f"=== FR30 pinned level {level}: ChebFSI K={K} block={m} deg {deg0}->{deg_max} lam_max=48 tol={tol:g} resume={resume} OMP_NUM_THREADS={os.environ.get('OMP_NUM_THREADS')} pid={os.getpid()} ===")
    geo = D.geometry('fr30', level); del geo['G']
    n = geo['n']; N = 2 * n
    geo['ea'] = geo['ea'].astype(np.int32); geo['eb'] = geo['eb'].astype(np.int32)
    log(f"   geometry: n={n} dim={N} panels={len(geo['ea'])} boundary tiles {(geo['deg'] < 24).sum()} links {geo['label_counts']} ({geo['build_s']:.1f}s, rss {rss_gb():.2f} GB)")
    H = build_H_per_axis(geo, log); del geo['eax'], geo['lab']
    herm = H - H.getH(); hd = float(np.abs(herm.data).max()) if herm.nnz else 0.0; del herm; assert hd == 0.0
    log(f"   H = 24 I - A: nnz {H.nnz} ({H.nnz/n:.3f}/tile), {(H.data.nbytes + H.indices.nbytes + H.indptr.nbytes)/1e9:.3f} GB, max|H-H^+|={hd:.1e}, rss {rss_gb():.2f} GB")
    if level <= 5:
        import phase5a_controls as pc
        from independent_clifford_q8_audit import FR30, tiles_at_level, panel_edges
        tiles = tiles_at_level(FR30, level); _, edges = panel_edges(tiles)
        Href = pc.build_H(n, edges, pc.clifford_links(tiles, edges), np.full(n, 24.0)); dev = H - Href; dev = float(np.abs(dev.data).max()) if dev.nnz else 0.0
        log(f"   validation vs object builders: max|dH| = {dev:.1e}"); assert dev == 0.0; del tiles, edges, Href
    rng = np.random.default_rng(7); p0 = 0; nmv = 0; elapsed0 = 0.0
    ck = load_newest(nm['ck']) if resume else None
    if ck is not None:
        X = np.ascontiguousarray(ck['X']); p0 = int(ck['pass_']) + 1; nmv = int(ck['nmv']); elapsed0 = float(ck['elapsed'])
        rng.bit_generator.state = json.loads(str(ck['rng_state']))
        X, th, res, orth = rayleigh_ritz(H, X); nmv += 1
        log(f"   resumed from checkpoint: pass {p0-1} done, {nmv} block matvecs, elapsed {elapsed0:.0f}s; re-Ritz theta_1={th[0]:.7f} res[:K] max {res[:K].max():.2e}")
    else:
        X = rng.standard_normal((N, m)) + 1j * rng.standard_normal((N, m))
        X, th, res, orth = rayleigh_ritz(H, X); nmv += 1
        log(f"   random start: theta_1={th[0]:.7f} theta_m={th[-1]:.7f} res[:K] max {res[:K].max():.2e} orth {orth:.1e} rss {rss_gb():.2f} GB")
    lam_lo = float(th[0]); b = 48.0; t_solve = time.time(); gen = p0
    log(f"   {'pass':>4} {'deg':>3} {'nmv':>6} {'theta_1':>10} {'theta_2':>10} {'theta_3':>10} {'theta_4':>10} {'res_1':>8} {'res_2':>8} {'res_3':>8} {'res_4':>8} {'kramers':>8} {'gap34-1':>9} {'orth':>7} {'pass_s':>6} {'elapsed':>8} {'rss':>5}")
    converged = False
    for p in range(p0, max_passes):
        tp = time.time(); deg = min(deg_max, int(deg0 * 1.25 ** p))
        a = float(th[-1]); e = (b - a) / 2.0; c = (b + a) / 2.0; a0 = lam_lo - 0.05 * (a - lam_lo) - 1e-3
        sigma = e / (a0 - c); sigma1 = sigma
        Y = H @ X; Y -= c * X; Y *= (sigma1 / e); nmv += 1
        for i in range(2, deg + 1):
            sigma_new = 1.0 / (2.0 / sigma1 - sigma)
            Z = H @ Y; Z -= c * Y; Z *= (2.0 * sigma_new / e); Z -= (sigma * sigma_new) * X; nmv += 1
            X = Y; Y = Z; del Z; sigma = sigma_new
        del X
        X, th, res, orth = rayleigh_ritz(H, Y); nmv += 1; del Y
        lam_lo = min(lam_lo, float(th[0])); worst = float(res[:K].max()); elapsed = elapsed0 + time.time() - t_solve
        log(f"   {p:>4} {deg:>3} {nmv:>6} {th[0]:>10.7f} {th[1]:>10.7f} {th[2]:>10.7f} {th[3]:>10.7f} {res[0]:>8.1e} {res[1]:>8.1e} {res[2]:>8.1e} {res[3]:>8.1e} {th[1]-th[0]:>8.1e} {th[2]-th[0]:>9.2e} {orth:>7.1e} {time.time()-tp:>6.0f} {elapsed:>8.0f} {rss_gb():>5.2f}")
        try:
            save_ckpt(nm['ck'], gen, X, th, res, p, nmv, rng, elapsed); gen += 1
        except Exception as ex: log(f"   checkpoint failed: {ex!r}")
        if worst <= tol: converged = True; break
    log(f"   {'converged' if converged else 'NOT converged (pass limit)'}: {nmv} block matvecs, solve {time.time()-t_solve:.0f}s (+{elapsed0:.0f}s before resume), total {time.time()-T0:.0f}s, max rss {rss_gb():.2f} GB")
    # ---------------------------------------------------------------- outputs
    V4 = np.ascontiguousarray(X[:, :4]); np.save(nm['vec'], V4)
    p1 = D.tile_density(V4[:, 0], True); p2 = D.tile_density(V4[:, 1], True); pg = 0.5 * (p1 + p2); np.save(nm['w'], pg)
    del X
    masks = D.interface_masks(geo); st = D.state_stats(pg, geo, masks); st2 = D.state_stats(0.5 * (D.tile_density(V4[:, 2], True) + D.tile_density(V4[:, 3], True)), geo, masks)
    rec = dict(level=level, n=n, dim=N, nnz=int(H.nnz), K=K, block=m, tol=tol, deg_ramp=[deg0, deg_max], converged=converged, block_matvecs=nmv,
               eigenvalues=th[:8].tolist(), residuals=res[:8].tolist(), kramers_split=float(th[1] - th[0]), gap_to_second_pair=float(th[2] - th[0]),
               eigenvector_angle_bound=float(res[0] / (th[2] - th[0])), ipr=st['ipr'], ipr_n=st['ipr_n'], ipr_vec1=D.IPR(p1), ipr_vec2=D.IPR(p2), P=1 / st['ipr'],
               S2={d: st['S2'][d] for d in range(1, level + 1)}, local_D2=st['local_D2'], interface_weight={d: st['interface_weight'][d] for d in (1, 2, 3)},
               interface_fraction={d: st['interface_fraction'][d] for d in (1, 2, 3)}, boundary_weight=st['boundary_weight'], boundary_fraction=st['boundary_fraction'],
               s50=st['s50'], s90=st['s90'], child_weights_depth1=st['child_weights_depth1'], second_pair=dict(eigenvalue=float(th[2]), ipr_n=st2['ipr_n'], interface_weight_1=st2['interface_weight'][1]),
               solve_seconds=time.time() - t_solve + elapsed0, total_seconds=time.time() - T0, max_rss_gb=rss_gb(), files=nm, omp=os.environ.get('OMP_NUM_THREADS'))
    with open(nm['js'], 'w') as f: json.dump(rec, f, indent=1, default=D.conv)
    log(f"   RESULT level {level}: lambda_1 = {th[0]:.7f} (res {res[0]:.1e}), pair 2 at {th[2]:.7f}, gap {th[2]-th[0]:.3e}, angle bound {rec['eigenvector_angle_bound']:.1e}")
    log(f"   ground state: IPR*n = {st['ipr_n']:.4f} (vec1 {D.IPR(p1)*n:.4f}, vec2 {D.IPR(p2)*n:.4f}), P = {1/st['ipr']:.1f}, s50 {st['s50']}, s90 {st['s90']}, bw {st['boundary_weight']:.6f} [{st['boundary_fraction']:.4f}]")
    log(f"   S2(d) d=1..L: {[f'{st['S2'][d]:.6g}' for d in range(1, level+1)]}  local D2: {np.round(st['local_D2'], 3).tolist()}")
    log(f"   interface weights d=1,2,3: {[round(st['interface_weight'][d], 5) for d in (1,2,3)]} [fractions {[round(st['interface_fraction'][d], 4) for d in (1,2,3)]}]; second pair IPR*n {st2['ipr_n']:.4f}")
    log(f"   saved {nm['vec']}, {nm['w']}, {nm['js']}")
    return rec

# ---------------------------------------------------------------- exact rational certification
def certify(level, scale_bits=24, chunk=512):
    """Rigorous upper bound lambda_min(H) <= <p,Hp>/<p,p> for p = round(2^S psi) (Gaussian integers), evaluated exactly:
    numpy int64 per chunk (|entries| <= 2^S, |H entries| <= 24 -> products < 2^53, 512 per chunk < 2^62), Python ints across chunks."""
    from fractions import Fraction
    nm = names(level); log = Log(nm['log']); t0 = time.time()
    V = np.load(nm['vec']); psi = V[:, 0]; del V
    geo = D.geometry('fr30', level); del geo['G']; H = build_H_per_axis(geo, log); del geo
    Hr = np.rint(H.data.real).astype(np.int64); Hi = np.rint(H.data.imag).astype(np.int64)
    assert np.abs(H.data.real - Hr).max() < 1e-12 and np.abs(H.data.imag - Hi).max() < 1e-12
    rows = np.repeat(np.arange(H.shape[0], dtype=np.int64), np.diff(H.indptr)); cols = H.indices.astype(np.int64); del H
    S = 2 ** scale_bits; pr = np.rint(psi.real * S).astype(np.int64); pi = np.rint(psi.imag * S).astype(np.int64); del psi
    norm2 = 0
    for j in range(0, len(pr), chunk): norm2 += int((pr[j:j+chunk] * pr[j:j+chunk] + pi[j:j+chunk] * pi[j:j+chunk]).sum())
    num_re = 0; num_im = 0
    for j in range(0, len(rows), chunk):
        r = rows[j:j+chunk]; c = cols[j:j+chunk]; a = Hr[j:j+chunk]; b = Hi[j:j+chunk]
        qr = a * pr[c] - b * pi[c]; qi = a * pi[c] + b * pr[c]              # q = H_rc p_c
        num_re += int((pr[r] * qr + pi[r] * qi).sum()); num_im += int((pr[r] * qi - pi[r] * qr).sum())   # conj(p_r) q
    assert num_im == 0, 'Rayleigh quotient not real'
    q = Fraction(num_re, norm2); val = num_re / norm2
    log(f"   CERTIFIED (exact integer arithmetic, scale 2^{scale_bits}): lambda_min(H_pin level {level}) <= {num_re}/{norm2} = {val:.10f}   ({time.time()-t0:.0f}s, rss {rss_gb():.2f} GB)")
    with open(os.path.join(RES, f"phase5b_d_level7{'' if level == 7 else f'_L{level}'}_certified.json"), 'w') as f:
        json.dump(dict(level=level, numerator=str(num_re), denominator=str(norm2), value=val, scale_bits=scale_bits, seconds=time.time() - t0), f, indent=1)
    return q

if __name__ == '__main__':
    ap = argparse.ArgumentParser(); ap.add_argument('cmd'); ap.add_argument('level', type=int); ap.add_argument('--resume', action='store_true')
    ap.add_argument('--tol', type=float, default=1e-7); ap.add_argument('--block', type=int, default=16); ap.add_argument('--K', type=int, default=4)
    args = ap.parse_args()
    if args.cmd == 'run': run(args.level, args.resume, args.tol, args.block, args.K)
    elif args.cmd == 'certify': certify(args.level)
    else: raise SystemExit(__doc__)
