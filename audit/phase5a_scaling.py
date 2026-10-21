"""
Phase 5a / Task B1 steps (3)-(5): finite-size scaling of the tile IPR of the lowest pinned/free/trivial eigenstates
from the per-level JSON files written by audit/phase5a_edge_states.py, interface-network comparison, and the
multifractal / box-counting summary.  Pure post-processing; every number is read from the JSON files named below.
Run from the repository root:  python3 -u -I audit/phase5a_scaling.py [levels, default 3 4 5 6]
Output: audit/results/phase5a_scaling.txt and audit/results/phase5a_scaling.json
"""
import os, sys, json
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__)); RES = os.path.join(HERE, 'results')
levels = [int(x) for x in sys.argv[1:]] or [3, 4, 5, 6]
data = {}
for L in levels:
    f = os.path.join(RES, f'phase5a_edge_states_level{L}.json')
    if os.path.exists(f): data[L] = json.load(open(f))
levels = sorted(data)
out = open(os.path.join(RES, 'phase5a_scaling.txt'), 'w'); summary = {'levels': levels, 'sources': {L: f'audit/results/phase5a_edge_states_level{L}.json' for L in levels}}
def log(s=''):
    print(s, flush=True); out.write(s + '\n')
STORED = {'pinned': {2: 10.77695, 3: 9.37847, 4: 8.91963, 5: 8.79701, 6: 8.77013}, 'free': {2: 4.72646, 3: 5.11494, 4: 5.20970, 5: 5.24993},
          'pinned_ipr': {4: 0.00223, 5: 0.00061, 6: 0.00016}}
T_INTERFACE = {1: 8, 2: 53, 3: 269, 4: 1277, 5: 5597}   # phase 3: tiles touching top-level child interfaces (T_k)

log("=" * 100); log("1. SPECTRAL BOTTOMS (this run) vs stored values")
for L in levels:
    d = data[L]
    pin = d['pinned']; fr = d.get('free'); tp = d.get('trivial_pinned')
    log(f" level {L}: n={d['n']}  H_pin lambda_min={pin['lowest_eigenvalue']:.6f} (res {pin['lowest_residual']:.1e}; stored {STORED['pinned'].get(L)})"
        + (f"  H_free lambda_min={fr['lowest_eigenvalue']:.6f} (res {fr['lowest_residual']:.1e}; stored {STORED['free'].get(L)})" if fr else "")
        + (f"  trivial pinned lambda_min={tp['lowest_eigenvalue']:.6f}" if tp else "")
        + (f"  LOBPCG cross-check {pin['lobpcg_crosscheck']['eigenvalues'][0]:.6f}" if 'lobpcg_crosscheck' in pin else ""))

def alphas(ns, iprs):
    ns = np.array(ns, float); iprs = np.array(iprs, float)
    two = [float(-np.log(iprs[i+1] / iprs[i]) / np.log(ns[i+1] / ns[i])) for i in range(len(ns) - 1)]
    fit = np.polyfit(np.log(ns), np.log(iprs), 1) if len(ns) >= 2 else [np.nan, np.nan]
    return two, float(-fit[0])

log(); log("=" * 100); log("2. FINITE-SIZE SCALING OF THE TILE IPR  (IPR = sum_a p_a^2, p_a tile weight; IPR*n = 1 for a uniform state)")
log("   alpha defined by IPR ~ n^(-alpha): alpha = 1 extended (IPR*n const), alpha = 0 localized, 0 < alpha < 1 critical / fractal support")
scal = {}
for key, label, sel in [('pinned', 'H_pin Clifford ground state (index 0)', lambda d: d['pinned']['eigenpairs'][0]['ipr']),
                        ('pinned_avg8', 'H_pin Clifford, mean IPR of lowest 8 eigenvectors', lambda d: d['pinned']['avg_lowest8']['mean_ipr']),
                        ('pinned_avg_all', 'H_pin Clifford, mean IPR of all K computed eigenvectors', lambda d: d['pinned']['avg_all']['mean_ipr']),
                        ('free', 'H_free Clifford ground state (surface band)', lambda d: d['free']['eigenpairs'][0]['ipr']),
                        ('free_avg8', 'H_free Clifford, mean IPR of lowest 8', lambda d: d['free']['avg_lowest8']['mean_ipr']),
                        ('trivial_pinned', 'trivial connection, pinned (24 - A_0) ground state', lambda d: d['trivial_pinned']['eigenpairs'][0]['ipr']),
                        ('trivial_pinned_avg8', 'trivial connection, pinned, mean IPR of lowest 8', lambda d: d['trivial_pinned']['avg_lowest8']['mean_ipr']),
                        ('trivial_free', 'trivial connection, free (deg - A_0) ground state (= uniform, IPR*n = 1)', lambda d: d['trivial_free']['eigenpairs'][0]['ipr'])]:
    ns, iprs, Ls = [], [], []
    for L in levels:
        try: v = sel(data[L])
        except (KeyError, TypeError, IndexError): continue
        ns.append(data[L]['n']); iprs.append(v); Ls.append(L)
    if len(ns) < 2: continue
    two, afit = alphas(ns, iprs)
    scal[key] = {'levels': Ls, 'n': ns, 'ipr': iprs, 'ipr_n': [i * n for i, n in zip(iprs, ns)], 'alpha_two_point': two, 'alpha_fit': afit}
    log(f" {label}:")
    log("   level: " + "  ".join(f"{L:>10d}" for L in Ls)); log("   n    : " + "  ".join(f"{n:>10d}" for n in ns))
    log("   IPR  : " + "  ".join(f"{i:10.6f}" for i in iprs)); log("   IPR*n: " + "  ".join(f"{i*n:10.3f}" for i, n in zip(iprs, ns)))
    log("   two-point alpha (consecutive levels): " + ", ".join(f"{a:.3f}" for a in two) + f";  least-squares alpha over all listed levels: {afit:.3f}")
# previous-run level-6 value (only if level 6 was not reproduced here)
if 6 not in levels and 'pinned' in scal and 5 in scal['pinned']['levels']:
    ns = scal['pinned']['n'] + [8 ** 6]; iprs = scal['pinned']['ipr'] + [STORED['pinned_ipr'][6]]
    two, afit = alphas(ns, iprs)
    log(f" [previous run, NOT reproduced here] level 6 H_pin ground state IPR = 0.00016 (audit/results/phase5_bulk_bottom_lobpcg.txt), IPR*n = {0.00016*8**6:.1f};"
        f" including it: two-point alphas {', '.join(f'{a:.3f}' for a in two)}, fit alpha {afit:.3f}")
    scal['pinned_with_previous_level6'] = {'n': ns, 'ipr': iprs, 'alpha_two_point': two, 'alpha_fit': afit, 'note': 'level-6 value from the previous run (not reproduced)'}

log(); log("=" * 100); log("3. INTERFACE NETWORK REFERENCE: tiles touching top-level child interfaces, T_L = 8, 53, 269, 1277, 5597 (phase 3), fraction |I_1|/n")
Ts = [T_INTERFACE[L] for L in range(1, 6)]; nsT = [8 ** L for L in range(1, 6)]
twoT = [float(np.log(Ts[i+1] / Ts[i]) / np.log(8)) for i in range(4)]; fitT = float(np.polyfit(np.log(nsT), np.log(Ts), 1)[0])
log(f"   T_L ~ n^beta: two-point beta = {', '.join(f'{b:.3f}' for b in twoT)}; fit beta = {fitT:.3f} (levels 1-5); levels 3-5 fit beta = {float(np.polyfit(np.log(nsT[2:]), np.log(Ts[2:]), 1)[0]):.3f}")
log(f"   a state uniform on the depth-1 interface tiles would have IPR = 1/T_L, i.e. alpha_interface = beta = {fitT:.3f} and IPR*n = n/T_L = "
    + ", ".join(f"{8**L/T_INTERFACE[L]:.2f}" for L in range(1, 6)) + " (levels 1-5)")
summary['interface_reference'] = {'T': Ts, 'beta_two_point': twoT, 'beta_fit': fitT}
for L in levels:
    d = data[L]
    log(f"   level {L}: depth-1 interface tiles computed here |I_1| = {d['interface_tile_counts']['1']} (phase 3 T_L = {T_INTERFACE.get(L)}); all depths {d['interface_tile_counts']}")

log(); log("=" * 100); log("4. INTERFACE DEPTH PROFILE: weight of the state on depth-d interface tiles vs. tile fraction |I_d|/n (ratio > 1 = enrichment)")
prof = {}
for L in levels:
    d = data[L]; n = d['n']; frac = {k: v / n for k, v in d['interface_tile_counts'].items()}
    log(f" level {L}: tile fractions {{d: |I_d|/n}} = { {k: round(v, 4) for k, v in frac.items()} }")
    for key, lab in [('pinned', 'H_pin ground state'), ('pinned_avg8', 'H_pin mean lowest 8'), ('free', 'H_free ground state'), ('trivial_pinned', 'trivial pinned ground state')]:
        try:
            w = d['pinned']['eigenpairs'][0]['interface_weight'] if key == 'pinned' else d['pinned']['avg_lowest8']['mean_interface_weight'] if key == 'pinned_avg8' \
                else d['free']['eigenpairs'][0]['interface_weight'] if key == 'free' else d['trivial_pinned']['eigenpairs'][0]['interface_weight']
        except (KeyError, TypeError): continue
        ratios = {k: w[k] / frac[k] for k in w}
        prof[(L, key)] = {'weight': w, 'fraction': frac, 'enrichment': ratios}
        log(f"   {lab:28s}: weight {{d: w_d}} = { {k: round(v, 4) for k, v in w.items()} }  enrichment w_d/(|I_d|/n) = { {k: round(v, 3) for k, v in ratios.items()} }")
summary['interface_profile'] = {f'L{L}_{k}': v for (L, k), v in prof.items()}

log(); log("=" * 100); log("5. BOUNDARY WEIGHT (tiles with < 24 panels) of the ground states vs boundary tile fraction")
for L in levels:
    d = data[L]; n = d['n']; bf = d['n_boundary_tiles'] / n
    s = f" level {L}: boundary tile fraction {bf:.4f};"
    for key, lab in [('pinned', 'H_pin'), ('free', 'H_free'), ('trivial_pinned', 'trivial pinned')]:
        if key in d: s += f"  {lab} ground-state boundary weight {d[key]['eigenpairs'][0]['boundary_weight']:.4f} (mean lowest 8: {d[key]['avg_lowest8']['mean_boundary_weight']:.4f});"
    log(s)

log(); log("=" * 100); log("6. MULTIFRACTAL / BOX-COUNTING (H_pin ground state): S_q(d) = sum over the 8^d level-(L-d) children of (child weight)^q")
log("   uniform extended: S_2(d) = 8^(-d) (local dimension D_2(d) = 3 per depth step); single child: S_2 = 1 (D_2 = 0); D_2(d) := -log_2[S_2(d)/S_2(d-1)] (3 = uniform fill, 2 = surface-like)")
mf = {}
for L in levels:
    d = data[L]; n = d['n']
    for key, lab in [('pinned', 'H_pin ground state'), ('trivial_pinned', 'trivial pinned ground state'), ('free', 'H_free ground state')]:
        if key not in d: continue
        r = d[key]['eigenpairs'][0]
        S2 = np.array(r['box_S2']); S3 = np.array(r['box_S3'])
        D2 = [-np.log2(S2[k] / S2[k-1]) for k in range(1, L + 1)]
        D3 = [-np.log2(S3[k] / S3[k-1]) / 2 for k in range(1, L + 1)]   # (q-1) D_q with q=3 -> divide by 2
        mf[f'L{L}_{key}'] = {'S2': S2.tolist(), 'S3': S3.tolist(), 'D2_local': [float(x) for x in D2], 'D3_local': [float(x) for x in D3],
                             'ipr_q2': r['ipr'], 'ipr_q3': r['ipr_q3'], 'child_weights_depth1': r['child_weights_depth1']}
        log(f" level {L} {lab}: IPR_2 = {r['ipr']:.3e} (n*IPR_2 = {r['ipr']*n:.2f}), IPR_3 = {r['ipr_q3']:.3e} (n^2*IPR_3 = {r['ipr_q3']*n*n:.2f})")
        log(f"    S_2(d), d=0..{L}: {np.array2string(S2, precision=5)}   local D_2 per depth step: {np.round(D2, 3).tolist()}   (uniform: 3.0)")
        log(f"    S_3(d), d=0..{L}: {np.array2string(S3, precision=6)}   local D_3 per depth step: {np.round(D3, 3).tolist()}")
        if key == 'pinned': log(f"    top-level child weights (8 children, uniform = 0.125): {np.round(r['child_weights_depth1'], 4).tolist()}")
        # pinned, averaged over 8 lowest
        if key == 'pinned':
            S2m = np.array(d['pinned']['avg_lowest8']['mean_box_S2']); D2m = [-np.log2(S2m[k] / S2m[k-1]) for k in range(1, L + 1)]
            log(f"    mean over lowest 8: S_2(d) = {np.array2string(S2m, precision=5)}  local D_2: {np.round(D2m, 3).tolist()}")
            mf[f'L{L}_pinned_avg8'] = {'S2': S2m.tolist(), 'D2_local': [float(x) for x in D2m]}
summary['scaling'] = scal; summary['multifractal'] = mf

log(); log("=" * 100); log("7. SPECTRAL DATA NEAR THE BOTTOM (H_pin): lowest 8 eigenvalues, doublet gaps, span of the computed block, IPR*n of each")
for L in levels:
    d = data[L]; ev = np.array([r['eigenvalue'] for r in d['pinned']['eigenpairs']]); res = np.array([r['residual'] for r in d['pinned']['eigenpairs']])
    iprn = np.array([r['ipr_n'] for r in d['pinned']['eigenpairs']])
    log(f" level {L}: K={len(ev)} lowest {np.round(ev[:8], 6).tolist()}; lambda_K - lambda_1 = {ev[-1]-ev[0]:.5f}; max residual {res.max():.1e}; "
        f"IPR*n of the lowest 8: {np.round(iprn[:8], 2).tolist()}; IPR*n over all K: min {iprn.min():.2f} median {np.median(iprn):.2f} max {iprn.max():.2f}")
json.dump(summary, open(os.path.join(RES, 'phase5a_scaling.json'), 'w'), indent=1)
log(f"\nsaved {os.path.join(RES, 'phase5a_scaling.json')}")
