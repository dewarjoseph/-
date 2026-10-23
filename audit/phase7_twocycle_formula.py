#!/usr/bin/env python3
"""Phase VII (II.1): exhaustive check of Lemma F'.1 with det factors against explicit Q8 products.
For every one of the 6^8 = 1 679 616 geometry-compatible O(3) frame choices on the level-1 supertile and every one of the 21
two-cycles (centre -> octant -> centre, third axis m): explicit holonomy == 1  <=>  det M_a det M_b (M_a^T e_m . M_b^T e_m) = 1.
Usage: python -u -I audit/phase7_twocycle_formula.py -> audit/results/phase7_twocycle_formula.json"""
import os, sys, json, itertools
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); RES = os.path.join(HERE, 'results')
import numpy as np
import phase7_adversarial as A
ALL = np.array(list(itertools.product(range(6), repeat=8)), np.int8)
FRA = np.array([[A.FR[t][p] for p in range(6)] for t in range(8)])
mismatch = 0; classes = {'1': 0, '-1': 0, 'traceless': 0}
for s in range(0, len(ALL), 100000):
    P = ALL[s:s + 100000]; tw = A.analyse(P)[5]
    for i, ((a, b), k, l) in enumerate(A.TWO):
        m = 3 - k - l; dot = (FRA[a, P[:, a], m] * FRA[b, P[:, b], m]).sum(1); val = A.DET[a, P[:, a]] * A.DET[b, P[:, b]] * dot
        mismatch += int(((val == 1) != (tw[:, i] == 0)).sum()) + int(((val == -1) != (tw[:, i] == 1)).sum())
        classes['1'] += int((tw[:, i] == 0).sum()); classes['-1'] += int((tw[:, i] == 1).sum()); classes['traceless'] += int((tw[:, i] >= 2).sum())
out = {'frame_choices': len(ALL), 'two_cycles_checked': 21 * len(ALL), 'mismatches': mismatch, 'holonomy_classes': classes}
print(out); json.dump(out, open(os.path.join(RES, 'phase7_twocycle_formula.json'), 'w'), indent=1)
