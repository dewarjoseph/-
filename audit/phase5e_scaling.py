#!/usr/bin/env python3
"""Phase V-E, Section VI: finite-size scaling of the FR30 pinned edge E_m (level m = substitution depth, linear size 2^(m+1)).

FREEZE (run before the level-7 solve finishes; the output is committed before any level-7 eigenvalue below 8.79 exists):
  data   E_m for m = 2..6 from audit/results/phase5c_gap_scaling.json (stored, all re-verified in V-B/V-C), m = 1 recomputed.
  models fitted to the stored levels only, each giving an out-of-level prediction of E_7:
    G3   geometric, free ratio:      E_m = E_inf + A r^m           (exact through m = 4, 5, 6)     r = 2^-p, p free
    D2   Dirichlet ratio 1/4:        E_m = E_inf + A 4^-m          (exact through m = 5, 6)         p = 2 (quadratic band edge)
    D48  two Dirichlet-like terms:   E_m = E_inf + A 4^-m + B 8^-m (exact through m = 4, 5, 6)
    PL   power law, least squares:   E_m = E_inf + A 2^(-p m)      (m = 3..6, 3 parameters, 4 points)
    RT   ratio trend:                decrement ratio r_m = d_m/d_(m-1) extrapolated linearly in m (r_7 = 2 r_6 - r_5)
  Each model is also refitted with one level dropped (jackknife over the levels it uses) to give a spread.
  DECISION RULES fixed here, applied to the level-7 decrement ratio r_7 = (E_6 - E_7)/(E_5 - E_6):
    r_7 in [0.24, 0.26]  -> consistent with the Dirichlet law E - E_inf ~ L^-2 at the largest size
    r_7 in (0.20, 0.24)  -> consistent with a single geometric law with p slightly above 2 (G3); L^-2 disfavoured
    r_7 <= 0.20          -> the decrement ratio keeps falling: no single power law describes levels 4..7; E_inf estimates
                            from any one-term law are then biased high, and only the bracket is trustworthy
    r_7 >= 0.26          -> the ratio turned around (non-monotone; log-periodic modulation or crossover not excluded)
  The certified bracket 4.008189 <= E_inf <= 8.7701336 (V-B) is not affected by any of this.
EVALUATE: reads the level-7 result written by audit/phase5e_level7_runner.py and scores the frozen predictions.
Usage: python -u -I audit/phase5e_scaling.py freeze | evaluate
"""
import os, sys, json, time, types
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); RES = os.path.join(HERE, 'results')
import numpy as np
from scipy.optimize import least_squares

def stored():
    g = json.load(open(os.path.join(RES, 'phase5c_gap_scaling.json')))['pinned']
    E = {int(k): float(v) for k, v in g.items()}
    from independent_clifford_q8_audit import FR30, tiles_at_level, panel_edges
    from phase5a_controls import clifford_links, build_H
    t = tiles_at_level(FR30, 1); _, e = panel_edges(t)
    E[1] = float(np.linalg.eigvalsh(build_H(len(t), e, clifford_links(t, e), np.full(len(t), 24.0)).toarray())[0])
    return dict(sorted(E.items()))

def geometric(E, ms):                      # exact 3-point geometric fit
    a, b, c = (E[m] for m in ms); d1, d2 = a - b, b - c; r = d2 / d1; Einf = c - d2 * r / (1 - r)
    return {'E_inf': Einf, 'r': r, 'p': -np.log2(r), 'pred': lambda m: Einf + (c - Einf) * r ** (m - ms[-1])}
def dirichlet(E, ms):                      # exact 2-point fit with ratio 1/4
    b, c = E[ms[0]], E[ms[1]]; d = b - c; Einf = c - d / 3
    return {'E_inf': Einf, 'r': 0.25, 'p': 2.0, 'pred': lambda m: Einf + (c - Einf) * 0.25 ** (m - ms[-1])}
def d48(E, ms):                            # exact 3-point fit E_inf + A 4^-m + B 8^-m
    M = np.array([[1, 4.0 ** -m, 8.0 ** -m] for m in ms]); x = np.linalg.solve(M, [E[m] for m in ms])
    return {'E_inf': x[0], 'A': x[1], 'B': x[2], 'pred': lambda m: x[0] + x[1] * 4.0 ** -m + x[2] * 8.0 ** -m}
def powerlaw(E, ms):                       # least squares E_inf + A 2^(-p m)
    y = np.array([E[m] for m in ms]); mm = np.array(ms, float)
    f = lambda q: q[0] + q[1] * 2.0 ** (-q[2] * mm) - y
    s = least_squares(f, [y[-1] - 0.01, (y[0] - y[-1]) * 2.0 ** (2 * mm[0]), 2.0], x_scale=[1, 100, 1])
    q = s.x; return {'E_inf': q[0], 'A': q[1], 'p': q[2], 'rms': float(np.sqrt(np.mean(s.fun ** 2))), 'pred': lambda m: q[0] + q[1] * 2.0 ** (-q[2] * m)}
def ratio_trend(E, ms):                    # ms = last three levels used for two ratios
    a, b, c = (E[m] for m in ms); d1, d2 = a - b, b - c
    E0 = E[ms[0] - 1]; d0 = E0 - a; r1, r2 = d1 / d0, d2 / d1; r3 = 2 * r2 - r1
    return {'r_next': r3, 'pred': lambda m: c - d2 * r3 if m == ms[-1] + 1 else np.nan}

def freeze():
    E = stored(); out = {'frozen_at_utc': time.strftime('%Y-%m-%d %H:%M:%S', time.gmtime()), 'data_E_m': E,
                        'note': 'computed before any converged level-7 eigenvalue existed; see docstring for the decision rules'}
    d = {m: E[m - 1] - E[m] for m in range(2, 7)}; out['decrements'] = d; out['decrement_ratios'] = {m: d[m] / d[m - 1] for m in range(3, 7)}
    fits = {'G3': geometric(E, (4, 5, 6)), 'D2': dirichlet(E, (5, 6)), 'D48': d48(E, (4, 5, 6)), 'PL': powerlaw(E, (3, 4, 5, 6)), 'RT': ratio_trend(E, (4, 5, 6))}
    jack = {'G3': [geometric(E, (3, 4, 6)), geometric(E, (3, 5, 6)), geometric(E, (3, 4, 5))], 'D2': [dirichlet(E, (4, 5)), dirichlet(E, (4, 6))],
            'D48': [d48(E, (3, 4, 5)), d48(E, (3, 5, 6)), d48(E, (3, 4, 6))], 'PL': [powerlaw(E, (2, 4, 5, 6)), powerlaw(E, (2, 3, 5, 6)), powerlaw(E, (2, 3, 4, 6))]}
    out['models'] = {}
    for k, f in fits.items():
        rec = {kk: float(v) for kk, v in f.items() if kk != 'pred'}; rec['E7_pred'] = float(f['pred'](7))
        if k != 'RT': rec['E6_check'] = float(f['pred'](6)); rec['E8_pred'] = float(f['pred'](8))
        if k in jack:
            ps = [float(j['pred'](7)) for j in jack[k]]; einf = [float(j['E_inf']) for j in jack[k]]
            rec['jackknife_E7'] = ps; rec['jackknife_E_inf'] = einf
        out['models'][k] = rec
    preds = [m['E7_pred'] for m in out['models'].values()]
    out['E7_envelope'] = [min(preds), max(preds)]
    out['decision_rules_r7'] = {'[0.24,0.26]': 'Dirichlet L^-2 consistent', '(0.20,0.24)': 'single geometric law p>2 (G3) consistent; L^-2 disfavoured',
                                '<=0.20': 'ratio keeps falling: no single power law over levels 4..7', '>=0.26': 'ratio turned around (non-monotone)'}
    out['frozen_eigenstate_predictions_from_V-D'] = {'D2_window_6_7': [1.80, 2.00], 'depth1_interface_weight_max': 0.57, 'depth1_enrichment_min': 10,
                                                     'overlap_with_level6_state_in_centre_child_max': 0.14}
    json.dump(out, open(os.path.join(RES, 'phase5e_level7_prediction.json'), 'w'), indent=1)
    for k, m in out['models'].items(): print(k, {kk: (round(v, 7) if isinstance(v, float) else v) for kk, v in m.items()})
    print('E7 envelope', out['E7_envelope'])

def evaluate():
    P = json.load(open(os.path.join(RES, 'phase5e_level7_prediction.json'))); p7 = os.path.join(RES, 'phase5e_level7.json')
    if not os.path.exists(p7): print('level-7 result not present:', p7); return None
    L7 = json.load(open(p7)); E7 = float(L7['eigenvalues'][0]); E = {int(k): v for k, v in P['data_E_m'].items()}
    d7 = E[6] - E7; r7 = d7 / (E[5] - E[6])
    verdict = ('Dirichlet L^-2 consistent' if 0.24 <= r7 <= 0.26 else 'single geometric law p>2 consistent; L^-2 disfavoured' if 0.20 < r7 < 0.24
               else 'ratio keeps falling: no single power law over levels 4..7' if r7 <= 0.20 else 'ratio turned around (non-monotone)')
    out = {'E7': E7, 'residual': L7['residuals'][0], 'converged': L7['converged'], 'd7': d7, 'r7': r7, 'verdict': verdict,
           'errors': {k: m['E7_pred'] - E7 for k, m in P['models'].items()}, 'within_envelope': P['E7_envelope'][0] <= E7 <= P['E7_envelope'][1]}
    E2 = dict(E); E2[7] = E7
    out['refit_with_7'] = {'G3_5_6_7': {k: float(v) for k, v in geometric(E2, (5, 6, 7)).items() if k != 'pred'},
                           'D2_6_7': {k: float(v) for k, v in dirichlet(E2, (6, 7)).items() if k != 'pred'},
                           'D48_5_6_7': {k: float(v) for k, v in d48(E2, (5, 6, 7)).items() if k != 'pred'},
                           'PL_4_7': {k: float(v) for k, v in powerlaw(E2, (4, 5, 6, 7)).items() if k != 'pred'}}
    json.dump(out, open(os.path.join(RES, 'phase5e_level7_evaluation.json'), 'w'), indent=1); print(json.dumps(out, indent=1)); return out

if __name__ == '__main__':
    {'freeze': freeze, 'evaluate': evaluate}[sys.argv[1]]()
