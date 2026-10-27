#!/usr/bin/env python3
"""Phase XII: the frozen level-7 prediction scored, and the frozen two-sided extrapolation of the frontier floors.

1. phase12_preregistration_next.json (frozen 2026-10-25): P1 the order Y7(539311) > Y7(1387) > Y7(539291) > Y7(1389);
   P2 0.010 <= Y7(539311) - Y7(1387) <= 0.030.  Scored on the exact rational upper bounds of phase12_y7.jsonl.
2. phase12_preregistration_extrapolation.json (frozen 2026-10-27, before the inputs below existed):
   E_up  from Y5, Y6, Y7 by Aitken's Delta^2 (Y_L = E + A q^L);
   E_low from the sampled probes Lambda_R, R in {16, 18, 20, 22}, by least squares in Lambda_R = E - C / rho^2, rho = R - 311/175;
   an ordering of two floors is reported as [X] evidence only if both estimates agree in sign and the smaller margin exceeds the
   larger discrepancy |E_up - E_low|.  Nothing here certifies anything.
Usage: python -u -I audit/phase12_extrapolation.py -> audit/results/phase12_extrapolation.json"""
import os, json, itertools
from fractions import Fraction
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__)); RES = os.path.join(HERE, 'results')
RULES = {'1387': 184323, '539311': 539311, '1389': 184338, '539291': 539291}
PROBES = {n: [f'phase11_probe_{n}.json'] + [f'phase12_probe_{n}_R{R}.json' for R in (16, 18, 20, 22, 24, 26)] for n in RULES}
RC = Fraction(311, 175)
def JL(n):
    p = os.path.join(RES, n)
    if os.path.exists(p): return [json.loads(l) for l in open(p)]
    import gzip
    return [json.loads(l) for l in gzip.open(p + '.gz', 'rt')] if os.path.exists(p + '.gz') else []

def upper_bounds():
    """exact rational Y_L of the four rules, L = 3..7, from the stored records"""
    Y = {name: {} for name in RULES}
    srcs = [(3, 'phase11_frontier_X3.jsonl'), (4, 'phase11_frontier_X4.jsonl'), (5, 'phase11_frontier_X5.jsonl'), (6, 'phase11_orbit_Y6.jsonl')]
    for L, src in srcs:
        rows = {r['j']: r for r in JL(src)}
        for name, j in RULES.items():
            if j in rows: Y[name][L] = Fraction(int(rows[j]['upper_num']), int(rows[j]['upper_den']))
    for r in JL('phase12_y7.jsonl'):
        for name, j in RULES.items():
            if r['j'] == j: Y[name][r['L']] = Fraction(int(r['upper_num']), int(r['upper_den']))
    return Y

def score_prediction(Y):
    if not all(7 in Y[n] for n in RULES): return {'status': 'pending: not every Y7 exists'}
    y = {n: Y[n][7] for n in RULES}
    p1 = y['539311'] > y['1387'] > y['539291'] > y['1389']
    gap = y['539311'] - y['1387']; p2 = Fraction(1, 100) <= gap <= Fraction(3, 100)
    order = sorted(RULES, key=lambda n: -y[n])
    return {'Y7': {n: float(v) for n, v in y.items()}, 'order': order, 'P1_order': p1, 'gap_539311_minus_1387': float(gap),
            'P2_gap_in_[0.010,0.030]': p2, 'prediction_holds': p1 and p2,
            'gap_history': {L: float(Y['539311'][L] - Y['1387'][L]) for L in sorted(Y['1387']) if L in Y['539311']}}

def e_up(Y):
    out = {}
    for n in RULES:
        if not all(L in Y[n] for L in (5, 6, 7)): continue
        y5, y6, y7 = (float(Y[n][L]) for L in (5, 6, 7)); q = (y6 - y7) / (y5 - y6)
        rec = {'q': q, 'richardson_q_quarter': (4 * y7 - y6) / 3}
        if 0 < q < 1: rec['E_up'] = y7 - (y6 - y7) * q / (1 - q)
        out[n] = rec
    return out

def e_low():
    out = {}
    for n, files in PROBES.items():
        pts = []
        for f in files:
            p = os.path.join(RES, f)
            if os.path.exists(p): pts += [(r['R'], r['Lambda_R_upper']) for r in json.load(open(p))['records']]
        pts = sorted(set(pts))
        if len(pts) < 2: continue
        R = np.array([x for x, _ in pts], float); lam = np.array([y for _, y in pts]); rho = R - float(RC)
        A = np.c_[np.ones_like(rho), -1 / rho ** 2]; (E, Cc), *_ = np.linalg.lstsq(A, lam, rcond=None)
        out[n] = {'radii': [int(x) for x in R], 'Lambda': lam.tolist(), 'E_low': float(E), 'C': float(Cc),
                  'max_abs_residual': float(np.abs(A @ np.array([E, Cc]) - lam).max())}
    return out

def decide(up, low):
    disc = {n: abs(up[n]['E_up'] - low[n]['E_low']) for n in RULES if n in up and 'E_up' in up[n] and n in low}
    pairs = []
    for x, y in itertools.permutations(disc, 2):
        mu = up[x]['E_up'] - up[y]['E_up']; ml = low[x]['E_low'] - low[y]['E_low']
        if mu > 0 and ml > 0:
            ok = min(mu, ml) > max(disc[x], disc[y])
            pairs.append({'pair': [x, y], 'margin_up': mu, 'margin_low': ml, 'max_discrepancy': max(disc[x], disc[y]),
                          'verdict': f'[X] evidence that E_*({x}) > E_*({y})' if ok else 'not resolved by extrapolation'})
    return {'discrepancy': disc, 'pairs': pairs}

if __name__ == '__main__':
    Y = upper_bounds(); up = e_up(Y); low = e_low()
    out = {'Y': {n: {L: float(v) for L, v in sorted(Y[n].items())} for n in RULES}, 'prediction': score_prediction(Y),
           'E_up': up, 'E_low': low, 'decision': decide(up, low)}
    json.dump(out, open(os.path.join(RES, 'phase12_extrapolation.json'), 'w'), indent=1)
    print(json.dumps(out, indent=1))
