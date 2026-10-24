#!/usr/bin/env python3
"""Phase XI, Parts II-V: evaluation of the preregistered predictions and the census-wide closed-form curvature bounds.

  twins          predictor sign(U1(twin) - U1(r)) against outcome sign(Y5(twin) - Y5(r)) for the 40 preregistered classes
  counterfactual P1-P3 of the preregistration on the single-child neighbours of FR30 (4752) and 4753 (class 1387); P4 is in
                 phase11_mechanism.json (compare_4752_4753)
  census_bounds  Theorem XI.E/F on all 1098 classes from the radius-1 loop data (phase11_local_census.jsonl): the two-cycle
                 transport bound min sin^2(theta2/2) when every legal centre has a non-trivial two-cycle, and the flatness-radius
                 bound 2 sin^2(theta0/2)/(3 N_1) with N_1 <= 25 when every legal centre has a non-trivial two-cycle or triangle;
                 and the association of two-cycle-flat legal types with the level-4 / level-5 bottoms
Usage: python -u -I audit/phase11_analysis.py -> audit/results/phase11_analysis.json"""
import os, sys, json, math
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); RES = os.path.join(HERE, 'results')
import numpy as np
from scipy import stats
import phase11_chair as C, phase11_frontier as F
def J(n): return json.load(open(os.path.join(RES, n)))
def JL(n):
    p = os.path.join(RES, n); return [json.loads(l) for l in open(p)] if os.path.exists(p) else []
def cp(k, n):
    lo = stats.beta.ppf(0.025, k, n - k + 1) if k > 0 else 0.0; hi = stats.beta.ppf(0.975, k + 1, n - k) if k < n else 1.0; return [float(lo), float(hi)]

def twins():
    pre = J('phase11_preregistration.json'); loc = {r['rule']: r for r in JL('phase11_local_twins.jsonl')}; y5 = {r['j']: r for r in JL('phase11_frontier_twins_Y5.jsonl')}
    S = C.perm_matrix((1, 0, 2)); rows = []
    for r in pre['part_II_twin_criterion']['classes']:
        d = C.proper_decoration(r); tw = tuple(tuple(int(np.argmax((C.perm_matrix(p) @ S)[i])) for i in range(3)) for p in d)
        jr, jt = F.ext_index(d), F.ext_index(tw)
        if str(r) not in loc or 'x%d' % jt not in loc or jr not in y5 or jt not in y5: continue
        dU = loc['x%d' % jt]['U1'] - loc[str(r)]['U1']; dY = y5[jt]['float'] - y5[jr]['float']
        rows.append({'class': r, 'twin_j': jt, 'U1': loc[str(r)]['U1'], 'U1_twin': loc['x%d' % jt]['U1'], 'Y5': y5[jr]['float'], 'Y5_twin': y5[jt]['float'],
                     'dU1': dU, 'dY5': dY, 'correct': bool(np.sign(dU) == np.sign(dY))})
    k = sum(r['correct'] for r in rows); n = len(rows)
    rho = stats.spearmanr([r['dU1'] for r in rows], [r['dY5'] for r in rows]).statistic if n > 2 else None
    return {'n': n, 'correct': k, 'accuracy': k / n if n else None, 'ci95': cp(k, n) if n else None, 'spearman_dU1_dY5': float(rho) if rho is not None else None,
            'twin_higher_Y5': sum(r['dY5'] > 0 for r in rows), 'rows': rows}

def counterfactual():
    pre = J('phase11_preregistration.json')['part_V_counterfactuals']; loc = {r['rule']: r for r in JL('phase11_local_counterfactual.jsonl')}
    y5 = {r['j']: r for r in JL('phase11_frontier_counterfactual_Y5.jsonl')}; out = {}
    for base, nbs in (('4752', pre['neighbours_FR30']), ('4753', pre['neighbours_4753'])):
        jb = F.ext_index(C.proper_decoration(int(base)))
        if base not in loc or jb not in y5: continue
        rows = [{'j': j, 'U1': loc['x%d' % j]['U1'], 'Y5': y5[j]['float'], 'Y5_upper': y5[j]['upper'], 'types': loc['x%d' % j]['n_types1'],
                 'twocycle_flat_types': loc['x%d' % j]['types_without_nontrivial_twocycle']} for j in nbs if 'x%d' % j in loc and j in y5]
        b = {'U1': loc[base]['U1'], 'Y5': y5[jb]['float']}
        rho = float(stats.spearmanr([r['U1'] for r in rows], [r['Y5'] for r in rows]).statistic)
        signs = [np.sign(r['U1'] - b['U1']) == np.sign(r['Y5'] - b['Y5']) for r in rows]
        topY = max(rows, key=lambda r: r['Y5']); top3U = sorted(rows, key=lambda r: -r['U1'])[:3]
        out[base] = {'base': b, 'n_neighbours': len(rows), 'P1_spearman': rho, 'P1_pass': rho >= 0.8,
                     'P2_sign_accuracy': float(np.mean(signs)), 'P2_pass': float(np.mean(signs)) >= 0.8,
                     'P3_best_Y5_neighbour': topY['j'], 'P3_pass': topY['j'] in [r['j'] for r in top3U],
                     'neighbours_above_base_Y5': sum(r['Y5'] > b['Y5'] for r in rows),
                     'spearman_twocycle_flat_vs_Y5': float(stats.spearmanr([r['twocycle_flat_types'] for r in rows], [r['Y5'] for r in rows]).statistic),
                     'rows': sorted(rows, key=lambda r: -r['Y5'])}
    return out

def census_bounds():
    cen = {r['class']: r for r in J('phase10_census.json')['classes']}; loc = JL('phase11_local_census.jsonl')
    if not loc: return None
    rows = []
    for r in loc:
        c = int(r['rule']); two = r['twocycle_transport_bound']; th = r['min_theta_short']
        flat_bound = 2 * math.sin(th / 2) ** 2 / (3 * 25) if th > 1e-9 else 0.0
        rows.append({'class': c, 'Y4': cen[c]['Y4'], 'U1_phase10': cen[c]['U1'], 'U1': r['U1'], 'n_types1': r['n_types1'], 'twocycle_flat_types': r['types_without_nontrivial_twocycle'],
                     'short_loop_flat_types': r['types_without_short_loop'], 'twocycle_bound': two, 'flatness_bound': flat_bound, 'best_closed_form': max(two, flat_bound)})
    Y4 = np.array([r['Y4'] for r in rows]); flat = np.array([r['twocycle_flat_types'] > 0 for r in rows])
    mw = stats.mannwhitneyu(Y4[~flat], Y4[flat], alternative='greater') if flat.any() and (~flat).any() else None
    top = sorted(rows, key=lambda r: -r['Y4'])
    return {'classes': len(rows), 'max_abs_U1_difference_vs_phase10': float(max(abs(r['U1'] - r['U1_phase10']) for r in rows)),
            'classes_all_centres_twocycle_frustrated': int((~flat).sum()), 'classes_with_twocycle_flat_types': int(flat.sum()),
            'classes_with_a_flat_short_loop_centre': sum(r['short_loop_flat_types'] > 0 for r in rows),
            'min_closed_form_bound': min(r['best_closed_form'] for r in rows), 'max_closed_form_bound': max(r['best_closed_form'] for r in rows),
            'median_Y4_twocycle_frustrated': float(np.median(Y4[~flat])) if (~flat).any() else None, 'median_Y4_with_flat': float(np.median(Y4[flat])) if flat.any() else None,
            'mannwhitney_p_frustrated_higher': float(mw.pvalue) if mw else None,
            'top20_by_Y4_with_twocycle_flat_types': [r['class'] for r in top[:20] if r['twocycle_flat_types'] > 0],
            'rows': rows}

if __name__ == '__main__':
    out = {'twins': twins(), 'counterfactual': counterfactual(), 'census_bounds': census_bounds()}
    json.dump(out, open(os.path.join(RES, 'phase11_analysis.json'), 'w'), indent=1, default=float)
    print(json.dumps({k: ({kk: vv for kk, vv in v.items() if kk != 'rows'} if isinstance(v, dict) and 'rows' in v else
                          ({b: {kk: vv for kk, vv in x.items() if kk != 'rows'} for b, x in v.items()} if isinstance(v, dict) else v)) for k, v in out.items()}, indent=1, default=float))
