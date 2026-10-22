#!/usr/bin/env python3
"""Phase V-C, checklist item 4: does the pinned gap survive coarse-graining (k -> infinity)?

Inputs (all from stored, previously verified artifacts; nothing re-solved here):
  pinned FR30 bottoms lambda_0(k), k = 2..6 (Phase V-A, reproduced independently in Phase V-B Workstream A/D);
  certified bounds: E_bulk >= 72147403/18000000 (radius-2 3-block certificate, Phase V-B E2) and
                    E_bulk <= 19748585252900893/2251799811448142 (exact level-6 Rayleigh quotient, Phase V-B E1);
  trivial-connection pinned bottoms (same graph, no flux) and free-boundary FR30 bottoms (Phase V-A/V-B).
Extrapolation models (numerical, NOT rigorous): geometric decrement E_inf + A r^k (last three points), Dirichlet
E_inf + c 4^{-k} (box side 2^{k+1}), and E_inf + c 4^{-k} + d 8^{-k} (three points).  The rigorous statement is the
certified bracket, which already decides the question asked.
"""
import os, sys, json
from fractions import Fraction
HERE = os.path.dirname(os.path.abspath(__file__)); RES = os.path.join(HERE, 'results')
import numpy as np

PIN = {2: 10.776950512, 3: 9.378470210, 4: 8.919634360, 5: 8.797011315, 6: 8.770133629}
TRIV = {2: 4.751193, 3: 1.669512, 4: 0.502729, 5: 0.138602, 6: 0.036461}
FREE = {2: 4.726465, 3: 5.114941, 4: 5.209699, 5: 5.249931}
LOW = Fraction(72147403, 18000000); UP = Fraction(19748585252900893, 2251799811448142)

def main():
    ks = sorted(PIN); E = np.array([PIN[k] for k in ks]); d = -np.diff(E); r = d[1:] / d[:-1]
    out = {'pinned': PIN, 'decrements': d.tolist(), 'decrement_ratios': r.tolist(), 'certified_lower': float(LOW), 'certified_upper': float(UP),
           'certified_lower_exact': str(LOW), 'certified_upper_exact': str(UP)}
    # geometric from k=4,5,6
    rr = d[-1] / d[-2]; Eg = E[-1] - d[-1] * rr / (1 - rr)
    # Dirichlet 4^-k from k=5,6
    Ed = (4 * E[-1] - E[-2]) / 3
    # 4^-k + 8^-k from k=4,5,6
    A = np.array([[1, 4.0 ** -k, 8.0 ** -k] for k in (4, 5, 6)]); Em = np.linalg.solve(A, E[-3:])[0]
    out['extrapolations'] = {'geometric_last3': float(Eg), 'dirichlet_4^-k_last2': float(Ed), 'mixed_4^-k_8^-k_last3': float(Em)}
    # trivial: bottoms scale like pi^2-type 4^-k  (box side doubles)
    tr = np.array([TRIV[k] for k in ks]); out['trivial_ratio'] = (tr[1:] / tr[:-1]).tolist()
    out['trivial_times_4^k'] = [float(TRIV[k] * 4 ** k) for k in ks]
    lines = ["PHASE V-C ITEM 4: PINNED GAP UNDER COARSE-GRAINING",
             f" pinned FR30 bottoms k=2..6: {[round(x,6) for x in E]}",
             f" decrements: {np.round(d,6).tolist()}  ratios: {np.round(r,4).tolist()}  (1/4 = Dirichlet 1/side^2 law)",
             f" CERTIFIED (exact rationals): {LOW} = {float(LOW):.9f} <= E_bulk <= {float(UP):.12f}",
             f" extrapolations (numerical): geometric {Eg:.5f}; 4^-k {Ed:.5f}; 4^-k+8^-k {Em:.5f}",
             f" trivial connection (no flux): bottoms {[TRIV[k] for k in ks]}; ratio per level {np.round(out['trivial_ratio'],4).tolist()}; 4^k * bottom {np.round(out['trivial_times_4^k'],3).tolist()} -> 0 gap",
             f" free boundary FR30: {[FREE[k] for k in sorted(FREE)]} (surface band; bulk spectrum identical by the boundary-independence theorem)",
             " VERDICT: the infinite-volume gap is NONZERO, proved: E_bulk >= 4.008 (> 0). It is a bulk flux-frustration gap: the",
             " same graph with trivial links has E_bulk = 0 (bottoms fall by ~1/4 per level, i.e. 1/side^2), and the gap does not",
             " depend on the pinned boundary (pinned and free IDS converge to the same limit). Its size is O(1) in hopping units,",
             " i.e. at the lattice scale: m ~ (E_bulk)^(1/2)/a in a wave equation, or E_bulk/a in Hamiltonian units. It is a",
             " cutoff-scale mass, not a light mass; the model has no free parameter that could make it parametrically smaller than 1/a."]
    print('\n'.join(lines))
    with open(os.path.join(RES, 'phase5c_gap_scaling.json'), 'w') as f: json.dump(out, f, indent=1)
    with open(os.path.join(RES, 'phase5c_gap_scaling.txt'), 'w') as f: f.write('\n'.join(lines) + '\n')

if __name__ == '__main__': main()
