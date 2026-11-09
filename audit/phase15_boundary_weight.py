#!/usr/bin/env python3
"""Phase XV: the boundary weight of the low-energy states of the pinned Chair44 operator on the top-level interface Gamma_L.

Protocol frozen in audit/results/phase15_preregistration_boundary_weight.json (commit d8adbb1) before any value below existed.

  T_{L+1}   phase11_chair.supertile(dec, L + 1) in its natural order; tile i lies in copy c = i // 8^L (the first inflation's child
            index is the leading base-8 digit, because phase11_chair.inflate orders children tile-major)
  Gamma_L   panels (a, b, k) of phase11_chair.Patch.panels with copy(a) != copy(b): the TOP-LEVEL inter-copy panels only
  H         pinned H = 24 - A_U (phase11_chair.operators); H on T_{L+1} = (direct sum of the 8 copy blocks) - A_Gamma exactly
  A         psi_k (k = 0, 1, 2) of the copy block, extended by zero:  w = <psi|P_Gamma|psi>,  g = sum_Gamma |psi_a - U_ab psi_b|^2
  B         phi_k (k = 0, 1, 2) of H on T_{L+1}:  w^B, g^B, and the coupling c^B = <phi|A_Gamma|phi>
  check     0 <= lambda_L - lambda_{L+1} <= c^B_0  (exact bracketing identity, to rounding)
Usage: python -u -I audit/phase15_boundary_weight.py [Lmax=5] [rule=1387]  -> audit/results/phase15_boundary_weight.json"""
import os, sys, json, time, types
os.environ.setdefault('OMP_NUM_THREADS', '1')
sys.modules.setdefault('resource', types.SimpleNamespace(getrusage=lambda *a: types.SimpleNamespace(ru_maxrss=0), RUSAGE_SELF=0))
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); RES = os.path.join(HERE, 'results')
import numpy as np, scipy.sparse as sps, scipy.sparse.linalg as sla
import phase11_chair as C
OUT = os.environ.get('PHASE15_OUT', os.path.join(RES, 'phase15_boundary_weight.json')); T0 = time.time()
def log(*a): print(f'[{time.time() - T0:7.0f}s]', *a, flush=True)
K = 4                                                           # psi_0..psi_3: two Kramers pairs (Q8 in SU(2): H commutes with J = i sigma_y conj, J^2 = -1, so every level is doubly degenerate; the preregistered psi_0, psi_1, psi_2 are among them)
Y_STORED = {3: 9.955918832486077, 4: 9.51686612726269, 5: 9.392828542100569, 6: 9.367950157113038}   # exact upper bounds Y_L(1387), audit/results/phase12_extrapolation.json

def geometry(dec, L):
    """T_{L+1}: frames, panels, copy labels, Gamma mask"""
    G, T = C.supertile(dec, L + 1); P = C.Patch(G, T); a, b, k = P.panels()
    copy = np.arange(P.n) // 8 ** L; gam = copy[a] != copy[b]
    return G, T, P.n, a, b, k, copy, gam

def bottom(H, k=K, tol=1e-12, extra=3):
    """the k lowest eigenpairs. Dense for n <= 2048. Otherwise ARPACK 'SA' with k + extra vectors and a fixed start (a 'SA' run with
    k = 3 skipped a member of the dense cluster once in testing), then, for n <= 2^17, shift-invert about w_0 - 0.05, which returns
    the eigenvalues nearest the shift and so cannot skip one inside the cluster; the two must agree."""
    n = H.shape[0]
    if n <= 2048:
        w, V = np.linalg.eigh(H.toarray()); return w[:k], V[:, :k], {'solver': 'dense'}
    v0 = np.random.default_rng(0).standard_normal(n) + 0j
    w, V = sla.eigsh(H, k=k + extra, which='SA', tol=tol, ncv=max(64, 6 * (k + extra)), v0=v0); o = np.argsort(w); w, V = w[o], V[:, o]
    info = {'solver': 'arpack SA', 'k_computed': k + extra}
    if n <= 1 << 17:
        ws, Vs = sla.eigsh(H, k=k + extra, sigma=w[0] - 0.05, which='LM', tol=tol, v0=v0); o = np.argsort(ws); ws, Vs = ws[o], Vs[:, o]
        info.update(solver='arpack SA + shift-invert', max_disagreement=float(np.abs(ws[:k] - w[:k]).max())); w, V = ws, Vs
    info['residuals'] = [float(np.linalg.norm(H @ V[:, j] - w[j] * V[:, j])) for j in range(k)]
    return w[:k], V[:, :k], info

def as_spinor(v): return v.reshape(-1, 2)

def observables(psi, inc, nG, ga, gb, gU):
    """w, g, coupling, N for one (full-length, normalised) vector"""
    s = as_spinor(psi); p2 = (np.abs(s) ** 2).sum(1)
    jump = s[ga] - np.einsum('nij,nj->ni', gU, s[gb])
    coup = 2 * np.real(np.einsum('ni,nij,nj->', s[ga].conj(), gU, s[gb]))
    return {'w': float(p2[inc].sum()), 'g': float((np.abs(jump) ** 2).sum()), 'coupling': float(coup), 'N': float((nG * p2).sum())}

def layers(n_copy, a, b, seeds, dmax=6):
    """graph distance (within the copy) from the seed tiles, capped at dmax + 1"""
    adj = sps.csr_matrix((np.ones(len(a)), (a, b)), shape=(n_copy, n_copy)); adj = ((adj + adj.T) > 0).tocsr()
    d = np.full(n_copy, dmax + 1); d[seeds] = 0; front = np.zeros(n_copy, bool); front[seeds] = True
    for r in range(1, dmax + 1):
        nb = (adj @ front.astype(np.int8)) > 0; new = nb & (d > dmax); d[new] = r; front = new
    return d

def level(dec, L, do_B=True):
    t0 = time.time(); G, T, n, a, b, k, copy, gam = geometry(dec, L); m = 8 ** L
    U = C.link_matrices(G, a, b, k); H = C.hermitian(n, a, b, U, 24); assert abs(H - H.getH()).max() == 0
    ga, gb, gU = a[gam], b[gam], U[gam]
    nG = np.bincount(ga, minlength=n) + np.bincount(gb, minlength=n); inc = np.flatnonzero(nG > 0)
    rec = {'L': L, 'tiles_T_L': m, 'tiles_T_L+1': n, 'panels_T_L+1': int(len(a)), 'Gamma': int(gam.sum()),
           'Gamma_tile_pairs': int(len(set(zip(np.minimum(ga, gb).tolist(), np.maximum(ga, gb).tolist())))),
           'incident_tiles': int(len(inc)), 'n_Gamma_max': int(nG.max()), 'copies': []}
    log(f'L={L}: T_{L+1} {n} tiles, {len(a)} panels, |Gamma_L| = {rec["Gamma"]}, incident tiles {len(inc)}')
    # ---- A: the copy blocks
    H0 = H[:2 * m, :2 * m].tocsr()
    G0, T0_ = C.supertile(dec, L); HL = C.operators(G0, T0_)
    rec['copy_blocks_equal_H_T_L'] = bool(all(abs(H[2 * c * m:2 * (c + 1) * m, 2 * c * m:2 * (c + 1) * m] - HL).max() == 0 for c in range(8)))
    assert rec['copy_blocks_equal_H_T_L']                                          # [C]: one eigenproblem serves every copy
    w, V, info = bottom(HL); rec['lambda_L'] = [float(x) for x in w]; rec['A_solver'] = info
    for c in range(8):
        s, e = 2 * c * m, 2 * (c + 1) * m
        mine = (ga // m == c) | (gb // m == c); inside = (copy[a] == c) & (copy[b] == c)
        dl = layers(m, a[inside] - c * m, b[inside] - c * m, np.flatnonzero(nG[c * m:(c + 1) * m] > 0))
        cr = {'copy': c, 'Gamma_panels_at_copy': int(mine.sum()), 'incident_tiles': int((nG[c * m:(c + 1) * m] > 0).sum()), 'states': []}
        for j in range(K):
            psi = np.zeros(2 * n, complex); psi[s:e] = V[:, j]; psi /= np.linalg.norm(psi)
            ob = observables(psi, inc, nG, ga, gb, gU)
            ob['rayleigh_in_T_L+1_minus_lambda'] = float(np.real(np.vdot(psi, H @ psi)) - w[j])     # 0: <A_Gamma> vanishes on one copy
            p2 = (np.abs(as_spinor(V[:, j])) ** 2).sum(1)
            ob['layer_weight'] = [float(p2[dl == r].sum()) for r in range(7)]
            ob['layer_tiles'] = [int((dl == r).sum()) for r in range(7)]
            cr['states'].append(ob)
        cr['subspace3'] = {q: float(np.mean([st[q] for st in cr['states'][:3]])) for q in ('w', 'g', 'N')}
        rec['copies'].append(cr)
    log(f'  A: lambda_L {rec["lambda_L"]}, solver {info} [{time.time() - t0:.0f}s]')
    for q in ('w', 'g'):
        for j in range(K):
            vals = [cr['states'][j][q] for cr in rec['copies']]
            rec.setdefault(f'A_{q}_max', []).append(max(vals)); rec.setdefault(f'A_{q}_mean', []).append(float(np.mean(vals)))
        rec[f'A_{q}_subspace3_max'] = max(cr['subspace3'][q] for cr in rec['copies'])
    log(f'  A: w_max {rec["A_w_max"]}, g_max {rec["A_g_max"]}')
    # ---- B: the glued states on T_{L+1}
    if do_B:
        t1 = time.time(); w, V, info = bottom(H, tol=1e-10); rec['lambda_L+1'] = [float(x) for x in w]; rec['B_solver'] = info
        rec['B'] = [observables(V[:, j] / np.linalg.norm(V[:, j]), inc, nG, ga, gb, gU) for j in range(K)]
        d = rec['lambda_L'][0] - w[0]; c0 = rec['B'][0]['coupling']
        rec['bracketing'] = {'lambda_L_minus_lambda_L+1': float(d), 'coupling_B0': c0, 'N_B0': rec['B'][0]['N'],
                             'holds': bool(-1e-8 <= d <= c0 + 1e-8), 'ratio_drop_over_coupling': float(d / c0)}
        log(f'  B: lambda_L+1 {rec["lambda_L+1"]}, w {[x["w"] for x in rec["B"]]}, coupling {[x["coupling"] for x in rec["B"]]}, '
            f'bracketing {rec["bracketing"]} [{time.time() - t1:.0f}s]')
    rec['seconds'] = time.time() - t0
    return rec

def fit(Ls, ys):
    """slope p of log2 y = c - p L, with leave-one-out (jackknife) error"""
    Ls = np.asarray(Ls, float); ly = np.log2(np.asarray(ys, float))
    p = -np.polyfit(Ls, ly, 1)[0]; n = len(Ls)
    loo = [-np.polyfit(np.delete(Ls, i), np.delete(ly, i), 1)[0] for i in range(n)]
    se = float(np.sqrt((n - 1) / n * np.sum((np.array(loo) - np.mean(loo)) ** 2)))
    local = [float(ly[i] - ly[i + 1]) for i in range(n - 1)]
    return {'p': float(p), 'jackknife_se': se, 'loo': [float(x) for x in loo], 'max_loo_dev': float(max(abs(x - p) for x in loo)),
            'local_slopes': local}

def verdict(p):
    return 'PASS (Dirichlet-like, p_w >= 2.5)' if p >= 2.5 else 'FAIL (uniform-like, p_w <= 1.5)' if p <= 1.5 else 'intermediate: report'

def summarise(recs, Ls):
    s = {}
    for q in ('w', 'g'):
        for j in range(K):
            s[f'A_{q}_max_k{j}'] = fit(Ls, [recs[L][f'A_{q}_max'][j] for L in Ls])
            s[f'A_{q}_mean_k{j}'] = fit(Ls, [recs[L][f'A_{q}_mean'][j] for L in Ls])
        s[f'A_{q}_subspace3_max'] = fit(Ls, [recs[L][f'A_{q}_subspace3_max'] for L in Ls])
    LB = [L for L in Ls if 'B' in recs[L]]
    if len(LB) >= 3:
        for q in ('w', 'g', 'coupling'):
            s[f'B_{q}_k0'] = fit(LB, [recs[L]['B'][0][q] for L in LB])
        s['drop_lambda_L_minus_lambda_L+1'] = fit(LB, [recs[L]['bracketing']['lambda_L_minus_lambda_L+1'] for L in LB])
    s['primary'] = {'statistic': 'A_w_max_k0', **s['A_w_max_k0'], 'verdict': verdict(s['A_w_max_k0']['p'])}
    return s

if __name__ == '__main__':
    Lmax = int(sys.argv[1]) if len(sys.argv) > 1 else 5; spec = sys.argv[2] if len(sys.argv) > 2 else '1387'
    dec = C.rule(spec); assert spec != '1387' or dec == C.extended_decoration(184323)
    gamma_counts = {}
    for L in range(1, Lmax + 1):
        G, T, n, a, b, k, copy, gam = geometry(dec, L); gamma_counts[L] = int(gam.sum())
    ratios = {L: gamma_counts[L] / gamma_counts[L - 1] for L in range(2, Lmax + 1)}
    log('|Gamma_L|', gamma_counts, 'ratios', ratios)
    recs = {}
    for L in range(2, Lmax + 1):
        recs[L] = level(dec, L)
        json.dump({'rule': spec, 'protocol': 'audit/results/phase15_preregistration_boundary_weight.json (commit d8adbb1)',
                   'Gamma_counts': gamma_counts, 'Gamma_ratios': ratios, 'levels': recs}, open(OUT + '.partial', 'w'), indent=1)
    Ls = sorted(recs)
    cross = {L: {'lambda_L+1_from_B(L-1)': recs[L - 1]['lambda_L+1'][0], 'lambda_L_from_A(L)': recs[L]['lambda_L'][0]} for L in Ls if L - 1 in recs and 'lambda_L+1' in recs[L - 1]}
    ystore = {L + 1: {'lambda_L+1': recs[L]['lambda_L+1'][0], 'Y_stored': Y_STORED[L + 1], 'below_stored_upper': recs[L]['lambda_L+1'][0] <= Y_STORED[L + 1] + 1e-9}
              for L in Ls if 'lambda_L+1' in recs[L] and L + 1 in Y_STORED}
    out = {'rule': spec, 'protocol': 'audit/results/phase15_preregistration_boundary_weight.json (commit d8adbb1)',
                             'label': '[E] floating-point eigenvectors (ARPACK, shift-invert where n <= 2^17); |Gamma_L|, copy-block equality [C]',
                             'Gamma_counts': gamma_counts, 'Gamma_ratios': ratios, 'cross_check_A_vs_B': cross, 'check_against_stored_Y': ystore,
                             'levels': recs, 'fits': summarise(recs, Ls)}
    json.dump(out, open(OUT, 'w'), indent=1); os.path.exists(OUT + '.partial') and os.remove(OUT + '.partial')
    log('primary', out['fits']['primary'])
