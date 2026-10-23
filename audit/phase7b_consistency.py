#!/usr/bin/env python3
"""Phase VII-B (A): consistency audit of the level-1 frame enumeration.

Why 6^8 = 1 679 616 compatible frame assignments give 6561 + 1 672 288 = 1 678 849 certified gauge classes:
the certificate runs over distinct tree-gauge keys (the 41 fundamental-cycle holonomies, explicit Q8 products, root = centre
tile).  Equal keys => gauge-equivalent connections => unitarily equivalent Laplacians, so one representative per key covers
every assignment.  This script recounts keys, lists the collision classes and identifies their mechanism:
  * constant permutation pi_x = pi for all 8 tiles: every link is s_a(k) s_b(k) * 1 (independent of pi), so the six fields
    are literally the same Abelian Z2 connection (the reflection-only control);
  * one tile with pi', the other seven with pi, versus the swap: links differ by -1 on a set of panels that is a gauge
    coboundary (same keys).
Usage: python -u -I audit/phase7b_consistency.py -> audit/results/phase7b_consistency.json"""
import os, sys, json, itertools, collections
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); RES = os.path.join(HERE, 'results')
import numpy as np
import phase7_adversarial as A

ALL = np.array(list(itertools.product(range(6), repeat=8)), np.int8)
proper = np.all(A.DET[np.arange(8)[None, :], ALL] == 1, axis=1)
keys, Ls = [], []
for s in range(0, len(ALL), 200000):
    L, k, *_ = A.analyse(ALL[s:s + 200000]); keys.append(k); Ls.append(L)
keys = np.concatenate(keys); Ls = np.concatenate(Ls)
uk_p = np.unique(keys[proper], axis=0); uk_i, inv, cnt = np.unique(keys[~proper], axis=0, return_inverse=True, return_counts=True)
inv = inv.ravel(); imp = np.nonzero(~proper)[0]
classes = [imp[inv == j] for j in np.nonzero(cnt > 1)[0]]
def kind(members):
    P = ALL[members]
    if all(len(set(row.tolist())) == 1 for row in P): return 'constant_pi'
    if len(members) == 2:
        a, b = P[0], P[1]; va, ca = collections.Counter(a.tolist()).most_common(1)[0]; vb, cb = collections.Counter(b.tolist()).most_common(1)[0]
        ta = [i for i in range(8) if a[i] != va]; tb = [i for i in range(8) if b[i] != vb]
        if ca == 7 and cb == 7 and ta == tb and a[ta[0]] == vb and b[tb[0]] == va: return 'one_tile_swap'
    return 'other'
kinds = collections.Counter(kind(m) for m in classes)
raw_equal = collections.Counter(bool(all(np.array_equal(Ls[m[0]], Ls[x]) for x in m)) for m in classes)
# for the swap pairs: the panel set where links differ, as a 0/1 cochain, must have zero sum (mod 2) on every fundamental cycle
def coboundary_ok(m):
    d = (Ls[m[0]] != Ls[m[1]]).astype(int)
    rel = {int(A.MUL[A.INVQ[Ls[m[0]][f]], Ls[m[1]][f]]) for f in np.nonzero(d)[0]}
    return rel <= {1}
cob = all(coboundary_ok(m) for m in classes if len(m) == 2)
key_overlap = len(set(map(bytes, uk_p)) & set(map(bytes, uk_i)))
out = {'assignments_all': len(ALL), 'assignments_proper': int(proper.sum()), 'assignments_improper': int((~proper).sum()),
       'keys_proper': len(uk_p), 'keys_improper': len(uk_i), 'keys_overlap_proper_improper': key_overlap, 'keys_total': len(uk_p) + len(uk_i) - key_overlap,
       'improper_class_sizes': {str(k): int(v) for k, v in collections.Counter(cnt.tolist()).items()},
       'collision_mechanisms': dict(kinds), 'collision_classes_with_identical_raw_links': {str(k): v for k, v in raw_equal.items()},
       'swap_pairs_differ_by_minus_one_only': cob,
       'check_sum': int(sum(len(m) for m in classes) + (cnt == 1).sum()) == int((~proper).sum())}
print(out); json.dump(out, open(os.path.join(RES, 'phase7b_consistency.json'), 'w'), indent=1)
