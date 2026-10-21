#!/usr/bin/env python3
"""Phase V-D: frozen held-out evaluation of the nonlocal boundary descriptors (protocol: audit/results/phase5d_protocol.json).

Data unit = one SYMMETRY CLASS of admissible decorations (class key: level-3 bottom to 7 decimals + level-4 class-count
multiset; 1098 classes, sizes 6 or 3), represented by one decoration; FR30 represents its own class.  Rules with a level-4
bottom: the 256 classes of the preregistered Phase V-B sample plus the classes computed in Phase V-C.
Target  Y4 = level-4 pinned bottom.  Flux-corrected residual r4 = Y4 - (flux model fitted on the TRAINING fold).
Models (ridge on standardised features, ridge alpha by inner 5-fold CV over a fixed grid; flux columns always included):
  M0 flux only (f_trl, f_m1)          M1 + 30 bounded-radius structural predictors (Phase V-B set)
  M2 + Y3 (previous-level edge)       M3 + child response c1(E), E in {6,7,8}
  M4 + c1 and gluing penalties gp_k(E), k in {1,2,4,8}       M5 + Y3 + c1 + gp (combined nonlocal)
  M6 + kmin(E) = lambda_min(K(E)): EXACT REFORMULATION CONTROL (its root is the target; not a mechanism)
Metrics: repeated rule-level 10-fold CV (20 repetitions, seeds 20261024+r): CV-R^2 of Y4, CV-RMSE, and the fraction of
the flux-only residual variance explained, 1 - SS(model)/SS(M0); mean +- sd over repetitions.  Leave-FR30-out prediction
of FR30's residual.  Intervention test: models trained on all rules predict the 18 Phase V-B controls (none in training);
report corr(predicted residual, actual residual) and the FR30-minus-control ordering.
"""
import os, sys, json, glob
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); RES = os.path.join(HERE, 'results')
import numpy as np

EGRID = (6.0, 7.0, 8.0); KS = (1, 2, 4, 8); ALPHAS = (1e-3, 1e-2, 1e-1, 1, 10, 100); NREP = 20; SEED0 = 20261024
STRUCT = ['enr1_trl', 'cv_m1', 'pair_m1', 'enr1_m1', 'enr2_m1', 'enr2_trl', 'enr3_m1', 'enr3_trl', 'cv_trl', 'cv_nt', 'hvar1_m1', 'hvar2_m1',
          'Ct_p1_p1', 'Ct_p1_m1', 'Ct_p1_trl', 'Ct_m1_m1', 'Ct_m1_trl', 'Ct_trl_trl', 'Cp_p1_p1', 'Cp_p1_m1', 'Cp_p1_trl', 'Cp_m1_m1', 'Cp_m1_trl',
          'Cp_trl_trl', 'loop21_f_m1', 'loop21_f_trl', 'loop22_f_m1', 'loop22_f_trl', 'f_i', 'f_j']

def nonlocal_cols(feat, which):
    out = []
    for f in feat:
        if 'c1' in which: out.append(f['c1'])
        if 'gp' in which: out += [f[f'gp{k}'] for k in KS]
        if 'kmin' in which: out.append(f['kmin'])
    return out

def design(rec, model, pred, feat):
    x = [pred['f_trl'], pred['f_m1']]
    if model == 'M1': x += [pred[s] for s in STRUCT]
    if model in ('M2', 'M5'): x.append(rec['Y3'])
    if model == 'M3': x += nonlocal_cols(feat, ('c1',))
    if model in ('M4', 'M5'): x += nonlocal_cols(feat, ('c1', 'gp'))
    if model == 'M6': x += nonlocal_cols(feat, ('kmin',))
    return x

def ridge_fit(X, y, alpha):
    mu, sd = X.mean(0), X.std(0); sd[sd == 0] = 1; Z = (X - mu) / sd
    A = np.c_[np.ones(len(Z)), Z]; P = alpha * np.eye(A.shape[1]); P[0, 0] = 0
    c = np.linalg.solve(A.T @ A + P, A.T @ y); return lambda Xn: np.c_[np.ones(len(Xn)), (Xn - mu) / sd] @ c

def fit_cv(X, y, rng):
    n = len(y); perm = rng.permutation(n); folds = np.array_split(perm, 5); best = None
    for a in ALPHAS:
        ss = 0
        for te in folds:
            tr = np.setdiff1d(perm, te); ss += ((ridge_fit(X[tr], y[tr], a)(X[te]) - y[te]) ** 2).sum()
        if best is None or ss < best[0]: best = (ss, a)
    return ridge_fit(X, y, best[1]), best[1]

def load():
    by = {}
    for fn in sorted(glob.glob(os.path.join(RES, 'phase5d_features_shard*.jsonl'))):
        for l in open(fn):
            try: r = json.loads(l)
            except json.JSONDecodeError: continue
            by[r['index']] = r
    D = json.load(open(os.path.join(RES, 'phase5b_sweep.json'))); pred = {r['index']: r['pred'] for r in D['records']}
    return [r for r in by.values()], pred

MODELS = ['M0', 'M1', 'M2', 'M3', 'M4', 'M5', 'M6']
def main():
    recs, pred = load(); recs = sorted(recs, key=lambda r: r['index']); n = len(recs)
    inadm = sum(not f['admissible'] for r in recs for f in r['feat'])
    y = np.array([r['Y4'] for r in recs]); fr = [i for i, r in enumerate(recs) if r['is_fr30']]
    Xs = {m: np.array([design(r, m, pred[r['index']], r['feat']) for r in recs], float) for m in MODELS}
    lines = []; P = lambda s='': (print(s), lines.append(s))
    P("PHASE V-D: HELD-OUT EVALUATION OF NONLOCAL BOUNDARY DESCRIPTORS (frozen protocol)")
    P(f" rule classes: {n}; feature evaluations at inadmissible energies: {inadm}; FR30 included: {bool(fr)}")
    res = {m: {'r2': [], 'rmse': [], 'frac': []} for m in MODELS}
    for rep in range(NREP):
        rng = np.random.default_rng(SEED0 + rep); perm = rng.permutation(n); folds = np.array_split(perm, 10)
        preds = {m: np.empty(n) for m in MODELS}
        for te in folds:
            tr = np.setdiff1d(perm, te)
            for m in MODELS:
                f, _ = fit_cv(Xs[m][tr], y[tr], rng); preds[m][te] = f(Xs[m][te])
        ss0 = ((y - preds['M0']) ** 2).sum(); sst = ((y - y.mean()) ** 2).sum()
        for m in MODELS:
            ss = ((y - preds[m]) ** 2).sum(); res[m]['r2'].append(1 - ss / sst); res[m]['rmse'].append(np.sqrt(ss / n)); res[m]['frac'].append(1 - ss / ss0)
    names = {'M0': 'flux only', 'M1': 'flux + 30 bounded-radius', 'M2': 'flux + Y3 (previous-level edge)', 'M3': 'flux + child response c1(E)',
             'M4': 'flux + c1 + gluing penalties gp_k(E)', 'M5': 'flux + Y3 + c1 + gp', 'M6': 'flux + kmin(E) [exact-reformulation control]'}
    P(f" {'model':<46} {'CV-R2 (Y4)':>16} {'CV-RMSE':>16} {'flux-residual variance explained':>34}")
    summary = {}
    for m in MODELS:
        a = {k: (float(np.mean(v)), float(np.std(v))) for k, v in res[m].items()}; summary[m] = a
        P(f" {m} {names[m]:<43} {a['r2'][0]:8.4f} +- {a['r2'][1]:.4f} {a['rmse'][0]:8.4f} +- {a['rmse'][1]:.4f} {a['frac'][0]:20.4f} +- {a['frac'][1]:.4f}")
    # leave-FR30-out
    out = {'n': n, 'summary': summary}
    if fr:
        i = fr[0]; tr = np.setdiff1d(np.arange(n), [i]); rng = np.random.default_rng(SEED0)
        f0, _ = fit_cv(Xs['M0'][tr], y[tr], rng); base = float(f0(Xs['M0'][[i]])[0])
        P(f" leave-FR30-out: actual Y4 {y[i]:.5f}; flux-only prediction {base:.5f} (residual {y[i]-base:+.4f})")
        out['fr30'] = {'Y4': float(y[i]), 'flux_pred': base, 'models': {}}
        for m in MODELS[1:]:
            fm, a = fit_cv(Xs[m][tr], y[tr], rng); p = float(fm(Xs[m][[i]])[0])
            out['fr30']['models'][m] = {'pred': p, 'explained_fraction_of_residual': (p - base) / (y[i] - base), 'alpha': a}
            P(f"   {m}: predicted {p:.5f}; fraction of FR30's flux residual explained {(p-base)/(y[i]-base):+.3f}")
    # interventions
    cp = os.path.join(RES, 'phase5d_controls.jsonl')
    if os.path.exists(cp):
        ctl = [json.loads(l) for l in open(cp)]; ctlpred = {json.loads(l)['system']: json.loads(l)['pred'] for l in open(os.path.join(RES, 'phase5b_controls.jsonl')) if json.loads(l)['level'] == 4}
        P(); P(" INTERVENTIONS (models trained on all rule classes; controls never in training): predicted vs actual flux residual")
        rng = np.random.default_rng(SEED0); fits = {m: fit_cv(Xs[m], y, rng)[0] for m in MODELS}
        y_c = np.array([c['Y4'] for c in ctl]); out['controls'] = {}
        Xc = {m: np.array([design({'Y3': None}, m, ctlpred[c['system']], c['feat']) if m not in ('M2', 'M5') else [np.nan] for c in ctl], dtype=object) for m in MODELS}
        base = np.array([fits['M0'](np.array([design({}, 'M0', ctlpred[c['system']], c['feat'])], float))[0] for c in ctl]); r_act = y_c - base
        for m in ('M1', 'M3', 'M4', 'M6'):
            pm = np.array([fits[m](np.array([design({}, m, ctlpred[c['system']], c['feat'])], float))[0] for c in ctl]); r_pred = pm - base
            cc = float(np.corrcoef(r_pred, r_act)[0, 1]); out['controls'][m] = {'corr': cc, 'r_pred': r_pred.tolist(), 'r_act': r_act.tolist()}
            P(f"   {m}: corr(predicted residual, actual residual) over {len(ctl)} controls = {cc:+.3f}; mean |error| {np.abs(r_pred-r_act).mean():.3f}")
        P("   per control (actual residual | M3 | M4 | M6 predicted):")
        for j, c in enumerate(ctl):
            P(f"     {c['system']:<12} {r_act[j]:+.3f} | {out['controls']['M3']['r_pred'][j]:+.3f} | {out['controls']['M4']['r_pred'][j]:+.3f} | {out['controls']['M6']['r_pred'][j]:+.3f}")
    json.dump(out, open(os.path.join(RES, 'phase5d_heldout.json'), 'w'), indent=1)
    open(os.path.join(RES, 'phase5d_heldout.txt'), 'w').write('\n'.join(lines) + '\n')

if __name__ == '__main__': main()
