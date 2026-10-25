#!/usr/bin/env python3
"""Phase XII, Part VIII: the preregistered predictive study (audit/results/phase12_preregistration.json; split, target, descriptor
families, model and metrics are frozen there and are read, not chosen, here).

Target Y5 (phase12_y5_census.jsonl, computed after the preregistration was committed).  Features from phase10_census.json.
Model per family: ridge regression, alpha 1e-3, standardised on the train split.  Predictions prioritise computation only:
an elimination always needs a certified bound (phase11_leaderboard.json), and the report counts how often a prediction-based
elimination would have been wrong.
Usage: python -u -I audit/phase12_predict.py -> audit/results/phase12_predict.json"""
import os, sys, json, math
import numpy as np
from scipy import stats
HERE = os.path.dirname(os.path.abspath(__file__)); RES = os.path.join(HERE, 'results')
def J(n): return json.load(open(os.path.join(RES, n)))
def JL(n): return [json.loads(l) for l in open(os.path.join(RES, n))]

def features(r):
    p = r['plaq_L3']; t = r['twocyc_L3']; np_ = sum(p.values()); nt = sum(t.values())
    f_p = [p['+1'] / np_, p['-1'] / np_, (p['i'] + p['j'] + p['k']) / np_]
    f_t = [t['+1'] / nt, t['-1'] / nt, (t['i'] + t['j'] + t['k']) / nt]
    return {'D1_plaquette_classes': f_p,
            'D2_radius_one_signature': [r['U0'], r['mu0'], r['n_types1'], r['U1_argmin_frequency']],
            'D3_radius_R_distributions': f_t + f_p,
            'D4_multiscale_frustration': [r['U0'], r['U1'], r['F1'], r['F2'], r['F3']],
            'D5_hierarchy': [r['Y1'], r['Y2'], r['Y3']]}
# cost: seconds per class to compute the family (Phase X census timings and phase11_local/phase12 measurements)
COST = {'D1_plaquette_classes': 'one T3 holonomy pass (< 1 s)', 'D2_radius_one_signature': 'legal 1-star closure + 1-star spectra (~5 s)',
        'D3_radius_R_distributions': 'one T3 holonomy pass (< 1 s)', 'D4_multiscale_frustration': 'U1 (inflated 1-stars, ~10 s) + free T1..T3 (< 1 s)',
        'D5_hierarchy': 'pinned T1..T3 eigenvalues (< 1 s)', 'target_Y5': 'pinned T5 (32 768 tiles) eigsh + exact Rayleigh (~3 s)'}

def ridge(X, y, alpha=1e-3):
    mu, sd = X.mean(0), X.std(0); sd[sd == 0] = 1; Z = (X - mu) / sd
    A = np.c_[np.ones(len(Z)), Z]; w = np.linalg.solve(A.T @ A + alpha * np.diag([0] + [1] * Z.shape[1]), A.T @ y)
    return lambda Xn: np.c_[np.ones(len(Xn)), (Xn - mu) / sd] @ w

if __name__ == '__main__':
    pre = J('phase12_preregistration.json'); tr, te = pre['split']['train'], pre['split']['test']
    cen = {r['class']: r for r in J('phase10_census.json')['classes']}; y5 = {r['class']: r['upper'] for r in JL('phase12_y5_census.jsonl')}
    assert set(y5) == set(cen), f'Y5 census incomplete: {len(y5)}'
    p10 = {r['class']: r['Y5'] for r in JL('phase10_y5.jsonl')}
    check = max(abs(p10[c] - y5[c]) for c in p10)                          # Phase X float Y5 against the new exact bounds
    lb = {r['class']: r for r in J('phase11_leaderboard.json')['rows']}
    F = {c: features(r) for c, r in cen.items()}; ytr = np.array([y5[c] for c in tr]); yte = np.array([y5[c] for c in te])
    out = {'n_train': len(tr), 'n_test': len(te), 'phase10_Y5_max_deviation': check, 'families': {}, 'single_features': {}}
    for fam in F[tr[0]]:
        Xtr = np.array([F[c][fam] for c in tr], float); Xte = np.array([F[c][fam] for c in te], float)
        model = ridge(Xtr, ytr); ptr, pte = model(Xtr), model(Xte); res = ytr - ptr; q05, q95 = np.quantile(res, [0.05, 0.95])
        cover = float(np.mean((yte >= pte + q05) & (yte <= pte + q95)))
        rec = {'spearman_test': float(stats.spearmanr(pte, yte).statistic), 'rmse_test': float(np.sqrt(np.mean((pte - yte) ** 2))),
               'interval_90_coverage_test': cover, 'interval_width': float(q95 - q05), 'cost': COST[fam]}
        for k in (10, 25):
            top = set(np.argsort(-yte)[:k]); sel = set(np.argsort(-pte)[:2 * k]); rec[f'top{k}_recall_in_model_top{2 * k}'] = len(top & sel) / k
        for tau in (8.5, 8.8):
            elim = pte + q95 < tau; rec[f'false_elimination_rate_tau_{tau}'] = (float(np.mean(yte[elim] >= tau)) if elim.any() else None)
            rec[f'eliminated_tau_{tau}'] = int(elim.sum())
        if 1387 in te: rec['post_hoc_rank_of_leader_1387_in_test'] = int((pte > pte[te.index(1387)]).sum()) + 1   # 1 = top (post hoc, not preregistered)
        out['families'][fam] = rec
        for i in range(Xte.shape[1]):
            out['single_features'][f'{fam}[{i}]'] = float(stats.spearmanr(Xte[:, i], yte).statistic)
    # the certified side, for comparison: classes of the test split proven inferior by certificates, and the frontier
    out['certified_test_status'] = {s: sum(lb[c]['status'] == s for c in te) for s in ('leader', 'contender', 'proven_inferior')}
    out['frontier_classes_in_test'] = [c for c in te if lb[c]['status'] != 'proven_inferior']
    out['cost_target'] = COST['target_Y5']
    json.dump(out, open(os.path.join(RES, 'phase12_predict.json'), 'w'), indent=1)
    print(json.dumps(out, indent=1)[:5000])
