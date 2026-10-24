#!/usr/bin/env python3
"""Phase X: merge every per-class result into the deliverable dataset, leaderboard and Pareto frontier.

Inputs: phase10_census.json (screening records), phase10_certify.jsonl (rigorous brackets), phase10_y5.jsonl, phase10_deep.jsonl,
phase10_ims.jsonl, phase10_periodic.jsonl; benchmarks and the FR30 certificates from earlier phases (files unchanged).
Outputs:
  phase10_dataset.json / .csv   one row per gauge class (all 1098), every quantity labelled by kind
  phase10_leaderboard.json/.csv the registered ranking (certified lower bound first), the Pareto frontier and the benchmarks
  phase10_descriptors.json      stage A descriptor audit: resolution, redundancy, the 937/938 falsification test, rank
                                correlation with Y4 (all classes) and Y5 (the registered random sample)
  phase10_criteria.json         cheap selection criteria against deeper levels (Spearman, top-20 recall)
Objectives for the Pareto frontier (all computable for every class): certified lower bound (max), certified bracket width
(min), level drift Y3 - Y4 (min), free/pinned gap at matched volume Y4 - F4 (min), single-frame perturbation sensitivity
(min), non-trivial plaquette fraction (max), number of legal 1-star types (min).
IMS and periodic records are keyed by a decoration index; they are mapped to the gauge class of that decoration.
Usage: python -u -I audit/phase10_analysis.py"""
import os, sys, json, csv, types, collections
from fractions import Fraction
sys.modules.setdefault('resource', types.SimpleNamespace(getrusage=lambda *a: types.SimpleNamespace(ru_maxrss=0), RUSAGE_SELF=0))
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); RES = os.path.join(HERE, 'results')
import numpy as np
def J(n): p = os.path.join(RES, n); return json.load(open(p)) if os.path.exists(p) else None
def JL(n): p = os.path.join(RES, n); return [json.loads(l) for l in open(p)] if os.path.exists(p) else []
FR30_CLASS = 1386

def neighbours_of(i):
    """the 16 decorations that change exactly one child's frame (one base-3 digit) of decoration i"""
    d = [(i // 3 ** k) % 3 for k in range(8)]; out = []
    for k in range(8):
        for v in range(3):
            if v != d[k]: out.append(i + (v - d[k]) * 3 ** k)
    return out

def prior_certificates():
    """certified bounds on E_* from earlier phases: FR30 (Phase VII Thm 7.1 at R = 12; Phase VIII exact Rayleigh quotient on the
    legal patch sigma^5(tau_59))"""
    p7, p8 = J('phase7_ims.json'), J('phase8_chain_m5.json')
    if not (p7 and p8): return {}
    return {FR30_CLASS: {'lower': float(Fraction(p7['12']['L_R_certified'])), 'lower_source': 'phase7_ims.json: Lambda_12 (2315 balls), Phase VII Thm 7.1',
                         'upper': float(Fraction(p8['rayleigh_upper_exact'])), 'upper_source': 'phase8_chain_m5.json: exact Rayleigh quotient on sigma^5(tau_59), 884736 tiles'}}

def external_benchmarks():
    """the brief's mandatory benchmarks that are not proper-census gauge classes; values are read from the earlier phases' files"""
    sc, seam, leg, c9, z = J('phase7b_scaling.json'), J('phase8_seamctl.json'), J('phase8_legality.json'), J('phase9_cert4.json'), J('phase10_z3_pairs.json')
    out = []
    for k, name in (('FR30_chi1', 'Abelian shadow chi_1 o U_FR30 (chi_3 is its x<->z mirror image)'), ('FR30_chi2', 'Abelian shadow chi_2 o U_FR30'),
                    ('Z2_reflect', 'Z2 reflection-only links on the FR30 hierarchy'), ('trivial', 'trivial links on the FR30 hierarchy')):
        v = sc[k]; out.append({'benchmark': name, 'control_of': 'the links (same geometry, same hierarchy)', 'Y_L_for_L_from_2': sc['Y_sequences_from_L2'][k],
                               'certified_upper_on_E_star': float(Fraction(v['rayleigh_upper_exact'])), 'certificate': 'exact Rayleigh quotient at L6',
                               'source': 'phase7b_scaling.json'})
    for k in ('iid1', 'coarse1', 'fine1', 'shuffle1', 'flip1,0.05'):
        out.append({'benchmark': f'scrambled control {k}', 'control_of': 'the hierarchy (FR30 frames scrambled; not a hull operator)', 'lambda_min_L5': seam[k]['E0'],
                    'illegal_1star_fraction': leg[k]['illegal_fraction'], 'ipr_n': seam[k]['ipr_n'], 'source': 'phase8_seamctl.json, phase8_legality.json'})
    for r in JL('phase10_periodic.jsonl'):
        out.append({'benchmark': f"periodic approximant: rule {r['class']}, level-{r['k']} supertile on the lattice 2^{r['k']} Lambda_7", 'control_of': 'aperiodicity (illegal seams)',
                    'bloch_minimum_numerical': r['E_per'], 'tiles_per_cell': r['tiles_per_cell'], 'source': 'phase10_periodic.jsonl'})
    out.append({'benchmark': 'rules 937 / 938', 'control_of': 'class counts (identical plaquette and two-cycle class counts)',
                'Y4_enclosure_937': [c9['937']['lower'], c9['937']['upper']], 'Y4_enclosure_938': [c9['938']['lower'], c9['938']['upper']],
                'certified_separation_L4': c9['certified_separation'], 'source': 'phase9_cert4.json'})
    if z and 'certificate_v2' in z:
        v = z['certificate_v2']
        out.append({'benchmark': 'Z^3 trace-field-matched pair (second geometry)', 'control_of': 'plaquette trace data in infinite volume',
                    'E_low_upper': v['E_low_upper'], 'E_high_lower': v['E_high_lower_free_cell'], 'certified_separation': v['certified_separation'],
                    'source': 'phase10_z3_pairs.json'})
    return out

def extended_candidates(ims_ext, by_class=None, cls_of=None):
    """stage C: the ten best distinct extended-space decorations (phase10_improper_top.json) with their certificates
    (phase10_improper_certify.jsonl) and localization bounds; j indexes the 6^8 decorations, census_index marks proper ones"""
    top = (J('phase10_improper_top.json') or {}).get('top10_distinct', []); cert = {r['j']: r for r in JL('phase10_improper_certify.jsonl')}; out = []
    for r in top:
        j = r['j']; c = cert.get(j, {}); lam = max((v['Lambda_R_certified'] for v in ims_ext[j].values() if v.get('Lambda_R_certified') is not None), default=None)
        ups = [x for x in (c.get('Y5_upper'), c.get('Y6_upper'), *(v.get('D_R_upper') for v in ims_ext[j].values())) if x is not None]
        if r['proper'] and by_class is not None:                                  # a proper decoration: its census class carries the certificates
            row = by_class[cls_of[r['census_index']]]; lam = row['best_certified_lower']; ups.append(row['best_certified_upper']); c = dict(c, Y6=row['Y6'])
        out.append({'j': j, 'proper': r['proper'], 'census_index': r['census_index'], 'Y3': r['Y3'], 'Y4': r['Y4'], 'Y5': r['Y5'], 'Y5_residual': r['Y5_residual'],
                    'child_dets': c.get('child_dets'), 'frames': c.get('frames'), 'period': c.get('period'), 'n_types1': c.get('n_types1'),
                    'Y4_certified': c.get('Y4_certified'), 'Y6': c.get('Y6'), 'best_certified_lower': lam, 'best_certified_upper': min(ups) if ups else None,
                    'ims': {R: {k: v.get(k) for k in ('Lambda_R_certified', 'Lambda_R_float', 'D_R_float', 'D_R_upper', 'mu_float')} for R, v in sorted(ims_ext[j].items())},
                    'decoration': r['decoration']})
    return out

def main():
    cen = J('phase10_census.json')['classes']; cert = {r['class']: r for r in JL('phase10_certify.jsonl')}
    y5 = {r['class']: r for r in JL('phase10_y5.jsonl')}; deep = {r['class']: r for r in JL('phase10_deep.jsonl')}
    cls_of = {i: r['class'] for r in cen for i in r['members']}; Y4 = {r['class']: r['Y4'] for r in cen}
    ims, ims_ext = collections.defaultdict(dict), collections.defaultdict(dict)
    for r in JL('phase10_ims.jsonl'):
        if r.get('class') is None: ims_ext[r['extended_index']][r['R']] = r      # stage C (extended-space) decorations
        else: ims[cls_of[r['class']]][r['R']] = r                                # a later record at the same R supersedes an earlier one
    # certified upper bounds on the Abelian-shadow floors: per shadow the best (smallest) exact Rayleigh quotient, then the largest
    # over the three shadows; for FR30 also Phase VII-B's level-6 certificates (phase7b_scaling.json; chi_3 = chi_1)
    sh = {d: {k: [x for kk, x in v.items() if kk.endswith('_upper')] for k, v in rec.items()} for d, rec in (J('phase10_shadows.json') or {}).items()}
    sc = J('phase7b_scaling.json')
    if sc and '4752' in sh:
        for k, name in (('chi1', 'FR30_chi1'), ('chi3', 'FR30_chi1'), ('chi2', 'FR30_chi2')): sh['4752'][k].append(float(Fraction(sc[name]['rayleigh_upper_exact'])))
    shadow_up = {cls_of[int(d)]: max(min(v) for v in rec.values()) for d, rec in sh.items()}
    per = collections.defaultdict(dict)
    for r in JL('phase10_periodic.jsonl'): per[cls_of[r['class']]][r['k']] = r
    import phase9_pair as P9, phase10_ims as I
    prior = prior_certificates(); rows = []
    for r in cen:
        c = r['class']; k = cert.get(c, {}); pl = r['plaq_L3']; npl = sum(pl.values()); nfr, kprim = I.frame_primitivity(P9.decoration(c))
        sens = max(abs(Y4[cls_of[j]] - r['Y4']) for j in neighbours_of(c))
        row = {'class': c, 'members': ' '.join(map(str, r['members'])), 'size': r['size'], 'contains_FR30': 4752 in r['members'],
               'Y1': r['Y1'], 'Y2': r['Y2'], 'Y3': r['Y3'], 'Y4': r['Y4'], 'F1': r['F1'], 'F2': r['F2'], 'F3': r['F3'], 'F4': r['F4'],
               'frames_reachable': nfr, 'frame_primitive_power': kprim,
               'U0': r['U0'], 'U1': r['U1'], 'mu0': r['mu0'], 'n_types1': r['n_types1'], 'n_types1_in_T5': r['n_types1_in_T5'], 'phi_self_loops': r['phi_self_loops'],
               'f_nontrivial_L3': 1 - pl['+1'] / npl, 'f_m1_L3': pl['-1'] / npl, 'drift_Y3_Y4': r['Y3'] - r['Y4'], 'free_pinned_gap_L4': r['Y4'] - r['F4'],
               'perturbation_sensitivity_Y4': sens, 'certified_lower_F3': k.get('certified_lower'), 'certified_upper_Y4': k.get('certified_upper'),
               'Y5': y5.get(c, {}).get('Y5'), 'Y5_residual': y5.get(c, {}).get('Y5_residual'), 'F5': y5.get(c, {}).get('F5'),
               'Y5_upper_certified': y5.get(c, {}).get('Y5_upper'), 'Y6': deep.get(c, {}).get('Y6'), 'Y6_residual': deep.get(c, {}).get('Y6_residual'),
               'U2': deep.get(c, {}).get('U2'), 'U3_top20': deep.get(c, {}).get('U3_top20')}
        best_ims = max((v['Lambda_R_certified'] for v in ims[c].values() if v.get('Lambda_R_certified') is not None), default=None)
        row['ims_lower_best'] = best_ims; row['ims_R'] = ' '.join(f"{R}:{v['Lambda_R_certified']:.6f}" for R, v in sorted(ims[c].items()) if v.get('Lambda_R_certified') is not None)
        row['ims_D_R'] = ' '.join(f"{R}:{v['D_R_float']:.6f}" for R, v in sorted(ims[c].items()) if v.get('D_R_float') is not None)
        d_up = min((v['D_R_upper'] for v in ims[c].values() if v.get('D_R_upper') is not None), default=None)
        row['Y6_upper_certified'] = deep.get(c, {}).get('Y6_upper'); row['D_R_upper_certified'] = d_up
        lows = [x for x in (row['certified_lower_F3'], best_ims, prior.get(c, {}).get('lower')) if x is not None]
        ups = [x for x in (row['certified_upper_Y4'], row['Y5_upper_certified'], row['Y6_upper_certified'], d_up, prior.get(c, {}).get('upper')) if x is not None]
        row['best_certified_lower'] = max(lows) if lows else None; row['best_certified_upper'] = min(ups) if ups else None
        row['abelian_shadow_upper_max'] = shadow_up.get(c)
        row['non_abelian_margin_certified'] = (row['best_certified_lower'] - shadow_up[c]) if c in shadow_up else None
        row['bracket_width'] = (row['best_certified_upper'] - row['best_certified_lower']) if lows and ups else None
        row['prior_certificates'] = prior[c]['lower_source'] + '; ' + prior[c]['upper_source'] if c in prior else ''
        row['periodic_bloch_min'] = ' '.join(f"k{k}:{v['E_per']:.4f}" for k, v in sorted(per[c].items()))
        rows.append(row)
    # Pareto frontier
    obj = [('best_certified_lower', 1), ('bracket_width', -1), ('drift_Y3_Y4', -1), ('free_pinned_gap_L4', -1), ('perturbation_sensitivity_Y4', -1),
           ('f_nontrivial_L3', 1), ('n_types1', -1)]
    ok = [r for r in rows if all(r[o] is not None for o, _ in obj)]
    def dominates(a, b): return all(s * a[o] >= s * b[o] for o, s in obj) and any(s * a[o] > s * b[o] for o, s in obj)
    front = [r for r in ok if not any(dominates(o, r) for o in ok)]
    for r in rows: r['pareto'] = r in front
    rank = sorted(rows, key=lambda r: -(r['best_certified_lower'] or -1e9))
    for i, r in enumerate(rank): r['rank_certified_lower'] = i + 1
    for i, r in enumerate(sorted(rows, key=lambda r: -r['Y4'])): r['rank_Y4'] = i + 1
    json.dump({'definitions': __doc__, 'rows': rows}, open(os.path.join(RES, 'phase10_dataset.json'), 'w'), default=float)
    keys = list(rows[0])
    with open(os.path.join(RES, 'phase10_dataset.csv'), 'w', newline='') as f:
        w = csv.DictWriter(f, fieldnames=keys); w.writeheader(); [w.writerow(r) for r in rows]
    top = rank[:30]
    json.dump({'ranking': 'best certified lower bound on E_* (max of the free-supertile certificate F3, any IMS certificate and prior certificates)',
               'top30': top, 'pareto_frontier': sorted(front, key=lambda r: -(r['best_certified_lower'] or 0)),
               'census_benchmarks': [r for r in rows if r['class'] in (FR30_CLASS, 937, 938)], 'external_benchmarks': external_benchmarks(),
               'extended_candidates': extended_candidates(ims_ext, {r['class']: r for r in rows}, cls_of)},
              open(os.path.join(RES, 'phase10_leaderboard.json'), 'w'), default=float, indent=1)
    with open(os.path.join(RES, 'phase10_leaderboard.csv'), 'w', newline='') as f:
        w = csv.DictWriter(f, fieldnames=keys); w.writeheader(); [w.writerow(r) for r in top]
    print(f"{len(rows)} rows; Pareto frontier {len(front)}; top by certified lower:", [(r['class'], round(r['best_certified_lower'], 4)) for r in rank[:8]])

def descriptor_audit():
    """stage A: which descriptors are redundant, which distinguish gauge classes, which pass the 937/938 test, and which predict"""
    from scipy.stats import spearmanr
    import phase10_hierarchy as H
    cen = {r['class']: r for r in J('phase10_census.json')['classes']}; cs = sorted(cen)
    F = {c: {k: v for part in H.features(cen[c]) for k, v in part.items()} for c in cs}
    for c in cs: F[c].update({k: cen[c][k] for k in ('Y1', 'Y2', 'Y3', 'F1', 'F2', 'F3', 'F4')})
    keys = sorted(F[cs[0]]); X = np.array([[F[c][k] for k in keys] for c in cs], float); y4 = np.array([cen[c]['Y4'] for c in cs])
    R = np.atleast_2d(spearmanr(X).statistic); np.fill_diagonal(R, 0)
    sample = J('phase10_stageB_selection.json')['random_sample_200']; y5 = {r['class']: r['Y5'] for r in JL('phase10_y5.jsonl')}
    si = [cs.index(c) for c in sample if c in y5]; ys = np.array([y5[cs[i]] for i in si])
    out = {}
    for j, k in enumerate(keys):
        a, b = F[937][k], F[938][k]; nd = int(len(np.unique(np.round(X[:, j], 9)))); row = np.abs(R[j]); ok = nd > 1 and np.isfinite(row).any()
        out[k] = {'distinct_values_over_classes': nd, 'max_abs_spearman_with_other': float(np.nanmax(row)) if ok else None,
                  'most_redundant_with': keys[int(np.nanargmax(row))] if ok else None, 'value_937': a, 'value_938': b,
                  'separates_937_938': bool(abs(a - b) > 1e-9 * max(1.0, abs(a))), 'spearman_Y4_all': float(spearmanr(X[:, j], y4).statistic) if nd > 1 else None,
                  'spearman_Y5_sample': float(spearmanr(X[si, j], ys).statistic) if len(si) > 10 and nd > 1 else None}
    json.dump({'n_classes': len(cs), 'n_Y5_sample': len(si), 'descriptors': out}, open(os.path.join(RES, 'phase10_descriptors.json'), 'w'), indent=1, default=float)
    print('descriptors failing the 937/938 test:', [k for k, v in out.items() if not v['separates_937_938']])

def criteria():
    """cheap selection criteria evaluated against deeper levels: Spearman rank correlation and top-k recall.  The Y5 target is the
    registered random sample only (the stage B selection is outcome-dependent)"""
    from scipy.stats import spearmanr
    cen = {r['class']: r for r in J('phase10_census.json')['classes']}; samp = set(J('phase10_stageB_selection.json')['random_sample_200'])
    y5 = {r['class']: r['Y5'] for r in JL('phase10_y5.jsonl') if r['class'] in samp}
    cheap = ['Y2', 'Y3', 'U0', 'U1', 'F2', 'F3', 'F4', 'mu0']; out = {}
    for target, vals, k in (('Y4', {c: r['Y4'] for c, r in cen.items()}, 20), ('Y5_sample', y5, 10)):
        cs = sorted(vals); y = np.array([vals[c] for c in cs]); row = {'n': len(cs), 'top_k': k}
        top = set(np.array(cs)[np.argsort(-y)[:k]])
        for key in cheap:
            x = np.array([cen[c][key] for c in cs]); rho = spearmanr(x, y).statistic
            rec = {f'recall_top{k}_in_top{m}': len(top & set(np.array(cs)[np.argsort(-x)[:m]])) / len(top) for m in (k, 2 * k, 5 * k)}
            row[key] = {'spearman': float(rho), **rec}
        out[target] = row
    json.dump(out, open(os.path.join(RES, 'phase10_criteria.json'), 'w'), indent=1); print(json.dumps(out)[:1500])

if __name__ == '__main__':
    main(); descriptor_audit(); criteria()
