#!/usr/bin/env python3
"""Phase X, Part V: does the substitution hierarchy add out-of-sample predictive information beyond local data?
Design fixed in audit/results/phase10_preregistration.json (part_V_test) before any census-wide result existed.

Rows: gauge classes (one each, so every split is grouped by class).  Targets: Y4 (all 1098 classes) and Y5 (the registered
random sample of 200 classes, phase10_y5.jsonl).  Feature sets (nested as registered):
  M1 local        plaquette class fractions f_m1, f_trl (level 3), two-cycle class fractions (+1, -1, traceless),
                  U0, U1, mu0, n_types1 (radius-1 environments)
  M2 loops        M1 + closed-walk moments m2..m8 (level 3) + 2x2 Wilson-loop fractions (V-B)
  M3 correlations M1 + V-B correlation statistics (Ct_*, Cp_*, pair_m1, cv_*)
  M4 hierarchy    M1 + M2 + M3 + depth enrichments enr1..3, hierarchical variances hvar1..2, Phi self-loops, Phi second
                  eigenvalue, frequency of the U1-minimising 1-star type
Learners: OLS on standardised features; sklearn HistGradientBoostingRegressor (defaults, random_state 0).  10-fold CV, seed
20261024.  Decision: hierarchy adds information iff, for both targets and both learners, the paired bootstrap 95% interval
(2000 resamples of classes) of RMSE(best of M1..M3) - RMSE(M4) lies entirely above 0.
Usage: python -u -I audit/phase10_hierarchy.py -> audit/results/phase10_hierarchy.json"""
import os, sys, json, time, types
sys.modules.setdefault('resource', types.SimpleNamespace(getrusage=lambda *a: types.SimpleNamespace(ru_maxrss=0), RUSAGE_SELF=0))
HERE = os.path.dirname(os.path.abspath(__file__)); RES = os.path.join(HERE, 'results')
import numpy as np
SEED = 20261024

def features(r):
    pl, tc, cp = r['plaq_L3'], r['twocyc_L3'], r['census_pred_L4']; npl = sum(pl.values()); ntc = sum(tc.values())
    m1 = {'f_m1': pl['-1'] / npl, 'f_trl': (pl['i'] + pl['j'] + pl['k']) / npl, 'tc_p1': tc['+1'] / ntc, 'tc_m1': tc['-1'] / ntc,
          'tc_trl': (tc['i'] + tc['j'] + tc['k']) / ntc, 'U0': r['U0'], 'U1': r['U1'], 'mu0': r['mu0'], 'n_types1': r['n_types1']}
    m2 = {f'm{p}': r['moments_L3'][p - 1] for p in range(2, 9)}; m2.update({k: cp[k] for k in ('loop22_f_m1', 'loop22_f_trl')})
    m3 = {k: cp[k] for k in cp if k.startswith(('Ct_', 'Cp_')) or k in ('pair_m1', 'cv_m1', 'cv_trl', 'cv_nt')}
    m4 = {k: cp[k] for k in ('enr1_m1', 'enr1_trl', 'enr2_m1', 'enr2_trl', 'enr3_m1', 'enr3_trl', 'hvar1_m1', 'hvar2_m1')}
    m4.update({'phi_self_loops': r['phi_self_loops'], 'phi_second': r['phi_second'], 'U1_argmin_frequency': r['U1_argmin_frequency']})
    return m1, m2, m3, m4

def design(recs):
    F = [features(r) for r in recs]
    def mat(parts):
        rows = [{k: v for i in parts for k, v in f[i].items()} for f in F]; keys = sorted(rows[0])
        return np.array([[row[k] for k in keys] for row in rows], float), keys
    return {'M1': mat([0]), 'M2': mat([0, 1]), 'M3': mat([0, 2]), 'M4': mat([0, 1, 2, 3])}

def cv_predict(X, y, learner):
    from sklearn.model_selection import KFold
    from sklearn.ensemble import HistGradientBoostingRegressor
    X = np.nan_to_num(X, nan=0.0); pred = np.zeros(len(y))
    for tr, te in KFold(10, shuffle=True, random_state=SEED).split(X):
        if learner == 'ols':
            mu, sd = X[tr].mean(0), X[tr].std(0); sd[sd == 0] = 1; A = np.c_[np.ones(len(tr)), (X[tr] - mu) / sd]
            c, *_ = np.linalg.lstsq(A, y[tr], rcond=None); pred[te] = np.c_[np.ones(len(te)), (X[te] - mu) / sd] @ c
        else:
            pred[te] = HistGradientBoostingRegressor(random_state=0).fit(X[tr], y[tr]).predict(X[te])
    return pred

def evaluate(recs, y, name):
    D = design(recs); rng = np.random.default_rng(SEED); out = {'n': len(y), 'sd': float(y.std())}
    for learner in ('ols', 'hgb'):
        P = {m: cv_predict(D[m][0], y, learner) for m in D}; err = {m: P[m] - y for m in P}
        rmse = {m: float(np.sqrt(np.mean(e ** 2))) for m, e in err.items()}
        best = min(('M1', 'M2', 'M3'), key=rmse.get); boots = []
        for _ in range(2000):
            i = rng.integers(0, len(y), len(y)); boots.append(np.sqrt(np.mean(err[best][i] ** 2)) - np.sqrt(np.mean(err['M4'][i] ** 2)))
        lo, hi = np.percentile(boots, [2.5, 97.5])
        calib = {m: float(np.polyfit(P[m], y, 1)[0]) for m in P}
        resid = sorted(((float(err['M4'][i]), int(recs[i]['class'])) for i in range(len(y))), key=lambda t: -abs(t[0]))[:10]
        out[learner] = {'rmse': rmse, 'r2': {m: 1 - rmse[m] ** 2 / float(y.var()) for m in rmse}, 'best_without_hierarchy': best,
                        'gain_rmse_best_minus_M4': float(np.sqrt(np.mean(err[best] ** 2)) - rmse['M4']), 'gain_ci95': [float(lo), float(hi)],
                        'calibration_slope': calib, 'largest_M4_residuals': resid, 'features': {m: D[m][1] for m in D}}
        print(name, learner, {m: round(v, 4) for m, v in rmse.items()}, 'best', best, 'gain CI', np.round([lo, hi], 4), flush=True)
    return out

def post_hoc_union(recs, y):
    """POST HOC, not registered: the registered comparator (the best of M1, M2, M3 taken separately) leaves the union of the loop
    and correlation descriptors untested, while M4 contains it.  M123 = M1 + M2 + M3 (no hierarchy descriptor) against M4, same
    folds and learners, isolates what the hierarchy descriptors add"""
    F = [features(r) for r in recs]; rows = [{k: v for i in (0, 1, 2) for k, v in f[i].items()} for f in F]; keys = sorted(rows[0])
    X123 = np.array([[row[k] for k in keys] for row in rows], float); X4 = design(recs)['M4'][0]; rng = np.random.default_rng(SEED + 1); out = {}
    for learner in ('ols', 'hgb'):
        e123, e4 = cv_predict(X123, y, learner) - y, cv_predict(X4, y, learner) - y; boots = []
        for _ in range(2000):
            i = rng.integers(0, len(y), len(y)); boots.append(np.sqrt(np.mean(e123[i] ** 2)) - np.sqrt(np.mean(e4[i] ** 2)))
        out[learner] = {'rmse_M123': float(np.sqrt(np.mean(e123 ** 2))), 'rmse_M4': float(np.sqrt(np.mean(e4 ** 2))),
                        'gain_ci95': [float(x) for x in np.percentile(boots, [2.5, 97.5])]}
        print('post hoc', learner, out[learner], flush=True)
    return out

if __name__ == '__main__':
    cen = {r['class']: r for r in json.load(open(os.path.join(RES, 'phase10_census.json')))['classes']}
    recs = [cen[c] for c in sorted(cen)]; y4 = np.array([r['Y4'] for r in recs]); out = {'Y4': evaluate(recs, y4, 'Y4')}
    y5 = {json.loads(l)['class']: json.loads(l)['Y5'] for l in open(os.path.join(RES, 'phase10_y5.jsonl'))}
    samp = json.load(open(os.path.join(RES, 'phase10_stageB_selection.json')))['random_sample_200']
    rs = [cen[c] for c in samp]; y5s = np.array([y5[c] for c in samp]); out['Y5_sample'] = evaluate(rs, y5s, 'Y5')
    dec = all(out[t][l]['gain_ci95'][0] > 0 for t in ('Y4', 'Y5_sample') for l in ('ols', 'hgb'))
    out['decision'] = 'hierarchy adds out-of-sample information' if dec else 'no reproducible gain from hierarchy descriptors'
    print(out['decision'])
    out['post_hoc_M123_vs_M4'] = {'status': 'post hoc, not part of the registered decision', 'Y4': post_hoc_union(recs, y4), 'Y5_sample': post_hoc_union(rs, y5s)}
    json.dump(out, open(os.path.join(RES, 'phase10_hierarchy.json'), 'w'), indent=1)
