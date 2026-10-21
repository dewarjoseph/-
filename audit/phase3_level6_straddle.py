"""
Independent test of the conjectured closed forms for the straddling plaquette class counts b_k(class):
  b_k(+1) = 15*4^k - 18*2^k + 49,  b_k(-1) = 5*4^k - 126,  b_k(j) = 4*4^k + 21,  b_k(i) = b_k(k) = 28   (k >= 3)
fitted on k = 3,4,5. This script recomputes b_k for k = 5 (consistency) and k = 6 (prediction) using an
array-based ownership map, enumerating only plaquettes that straddle the eight level-(k-1) children.
Run from the repository root:  python3 -u -I audit/phase3_level6_straddle.py [levels...]
"""
import os, sys, collections, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
from independent_clifford_q8_audit import FR30, tiles_at_level, clifford_link, q8label

def straddle_counts(lvl):
    t0 = time.time(); tiles = tiles_at_level(FR30, lvl); N = 2 ** (lvl + 1)
    O = -np.ones((N, N, N), dtype=np.int64)
    for a, (_, _, cs) in enumerate(tiles):
        idx = np.array(list(cs)); O[idx[:, 0], idx[:, 1], idx[:, 2]] = a
    assert (O >= 0).sum() == 7 * 8 ** lvl
    child = np.where(O >= 0, O // (8 ** (lvl - 1)), -1)
    frames = [t[0] for t in tiles]; cache = {}
    def link(a, b, d):
        key = (a, b, d)
        if key not in cache: cache[key] = clifford_link(frames[a], frames[b], np.array(d, int))
        return cache[key]
    cnt = collections.Counter(); straddle = 0; mixed = 0
    E = np.eye(2, dtype=complex)
    for (i, j) in [(0, 1), (1, 2), (0, 2)]:
        sl = [slice(0, N - 1) if ax in (i, j) else slice(0, N) for ax in range(3)]
        def shift(A, di, dj):
            s = [slice(di if ax == i else (dj if ax == j else 0), (N - 1 + di) if ax == i else ((N - 1 + dj) if ax == j else N)) for ax in range(3)]
            return A[tuple(s)]
        O0, O1, O2, O3 = shift(O, 0, 0), shift(O, 1, 0), shift(O, 1, 1), shift(O, 0, 1)
        present = (O0 >= 0) & (O1 >= 0) & (O2 >= 0) & (O3 >= 0)
        C0, C1, C2, C3 = shift(child, 0, 0), shift(child, 1, 0), shift(child, 1, 1), shift(child, 0, 1)
        mix_tile = present & ~((O0 == O1) & (O1 == O2) & (O2 == O3))
        mix_child = present & ~((C0 == C1) & (C1 == C2) & (C2 == C3))
        mixed += int(mix_tile.sum()); straddle += int(mix_child.sum())
        ei = [0, 0, 0]; ei[i] = 1; ej = [0, 0, 0]; ej[j] = 1
        steps = [(tuple(ei)), (tuple(ej)), tuple(-x for x in ei), tuple(-x for x in ej)]
        for (x, y, z) in zip(*np.nonzero(mix_child)):
            owners = [O0[x, y, z], O1[x, y, z], O2[x, y, z], O3[x, y, z]]
            W = E
            for q in range(4):
                a, b = owners[q], owners[(q + 1) % 4]
                if a != b: W = W @ link(a, b, steps[q])
            cnt[q8label(W)] += 1
    cls = {'1': cnt['+1'], '-1': cnt['-1'], 'i': cnt['+i'] + cnt['-i'], 'j': cnt['+j'] + cnt['-j'], 'k': cnt['+k'] + cnt['-k']}
    print(f"level {lvl}: inter-tile N_k={mixed} (formula {18*8**lvl-24*4**lvl+6*2**lvl}), straddling B_k={straddle} (formula {24*4**lvl-18*2**lvl}),"
          f" classes b_k={cls}  ({time.time()-t0:.0f}s)")
    pred = {'1': 15*4**lvl - 18*2**lvl + 49, '-1': 5*4**lvl - 126, 'j': 4*4**lvl + 21, 'i': 28, 'k': 28}
    print(f"   conjectured closed form: {pred}  match: {pred == cls}")
    return cls

for lvl in (int(x) for x in (sys.argv[1:] or ['3', '4', '5', '6'])):
    straddle_counts(lvl)
