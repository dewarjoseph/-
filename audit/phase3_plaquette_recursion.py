"""
Exact inheritance recursion for plaquette-curvature counts across the hierarchy and rigorous bounds on the
limiting frequencies.  Run from the repository root:  python3 -I audit/phase3_plaquette_recursion.py [maxlevel]
"""
import os, sys, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
from fractions import Fraction as Fr
from independent_clifford_q8_audit import FR30, tiles_at_level, panel_edges, clifford_link, q8label

maxlvl = int(sys.argv[1]) if len(sys.argv) > 1 else 4
counts = {}; interface_tiles = {}
for lvl in range(1, maxlvl + 1):
    tiles = tiles_at_level(FR30, lvl); owner, edges = panel_edges(tiles); cubes = set(owner)
    # child index of each tile: tiles are generated depth-first, 8^(lvl-1) consecutive tiles per level-1 child
    child = lambda a: a // (8 ** (lvl - 1))
    cache = {}
    def link(c1, c2):
        a, b = owner[c1], owner[c2]
        if a == b: return None
        d = (c2[0]-c1[0], c2[1]-c1[1], c2[2]-c1[2]); key = (a, b, d)
        if key not in cache: cache[key] = clifford_link(tiles[a][0], tiles[b][0], np.array(d, int))
        return cache[key]
    cnt = collections.Counter(); bcnt = collections.Counter(); total = mixed = straddle = 0
    for c in cubes:
        for (i, j) in [(0, 1), (1, 2), (0, 2)]:
            ei = [0, 0, 0]; ei[i] = 1; ej = [0, 0, 0]; ej[j] = 1
            c1 = (c[0]+ei[0], c[1]+ei[1], c[2]+ei[2]); c2 = (c1[0]+ej[0], c1[1]+ej[1], c1[2]+ej[2]); c3 = (c[0]+ej[0], c[1]+ej[1], c[2]+ej[2])
            if c1 in cubes and c2 in cubes and c3 in cubes:
                total += 1; ts = {owner[c], owner[c1], owner[c2], owner[c3]}
                if len(ts) > 1:
                    mixed += 1; W = np.eye(2, dtype=complex)
                    for x, y in ((c, c1), (c1, c2), (c2, c3), (c3, c)):
                        L = link(x, y)
                        if L is not None: W = W @ L
                    lab = q8label(W); cnt[lab] += 1
                    if len({child(a) for a in ts}) > 1: straddle += 1; bcnt[lab] += 1
    T = len({a for a, b, _, _, _ in edges if child(a) != child(b)} | {b for a, b, _, _, _ in edges if child(a) != child(b)})
    counts[lvl] = (total, mixed, cnt, straddle, bcnt); interface_tiles[lvl] = T
    print(f"level {lvl}: plaquettes={total} inter-tile N_k={mixed} straddling-children B_k={straddle} tiles-touching-child-interfaces T_k={T}")
    print(f"   labels: {dict(cnt)}\n   straddling labels b_k: {dict(bcnt)}")

print("\nINHERITANCE CHECK (conjugacy classes {1},{-1},{+-i},{+-j},{+-k}): Count_k(cls) - 8*Count_{k-1}(cls) == b_k(cls)")
labels = ['+1', '-1', '+i', '-i', '+j', '-j', '+k', '-k']
classes = {'1': ['+1'], '-1': ['-1'], 'i': ['+i', '-i'], 'j': ['+j', '-j'], 'k': ['+k', '-k']}
def cc(cnt, cl): return sum(cnt[l] for l in classes[cl])
for lvl in range(2, maxlvl + 1):
    ok_cls = all(cc(counts[lvl][2], c) - 8 * cc(counts[lvl-1][2], c) == cc(counts[lvl][4], c) for c in classes)
    ok_lab = all(counts[lvl][2][l] - 8 * counts[lvl-1][2][l] == counts[lvl][4][l] for l in labels)
    print(f" level {lvl}: exact for the 5 classes: {ok_cls}; exact for the 8 signed labels: {ok_lab} (signs of +-i,+-j,+-k depend on loop orientation/base point);"
          f"  N_k - 8 N_(k-1) = {counts[lvl][1] - 8*counts[lvl-1][1]} == B_k = {counts[lvl][3]}")
print("CLOSED FORM CHECK: B_k = 24*4^k - 18*2^k ; N_k = 18*8^k - 24*4^k + 6*2^k")
for lvl in range(1, maxlvl + 1):
    Bk = 24 * 4**lvl - 18 * 2**lvl; Nk = 18 * 8**lvl - 24 * 4**lvl + 6 * 2**lvl
    print(f" level {lvl}: B_k formula {Bk} vs measured {counts[lvl][3] if lvl>1 else counts[lvl][1]} ; N_k formula {Nk} vs measured {counts[lvl][1]}")

print("\nRIGOROUS BOUNDS ON LIMITING FREQUENCIES (using Count_k = 8 Count_{k-1} + b_k, 0 <= b_k <= B_k)")
K = maxlvl; tot = counts[K][2]
def bounds(cnt_val, Bform):
    lo = Fr(cnt_val, 8**K); hi = lo + sum(Fr(Bform(j), 8**j) for j in range(K + 1, 200))
    den = Fr(18)  # lim N_k/8^k = 18 (under the verified closed form)
    return float(lo / den), float(hi / den)
Bform = lambda j: 24 * 4**j - 18 * 2**j
for name, val in [("W != I", counts[K][1] - tot['+1']), ("Tr W = 0", sum(tot[l] for l in labels if l not in ('+1', '-1'))), ("W = -I", tot['-1'])]:
    lo, hi = bounds(val, Bform); print(f" {name:9s}: observed level-{K} fraction {val/counts[K][1]:.4f}; limit in [{lo:.4f}, {hi:.4f}]")
print(" (loose, assumption-free alternative: B_j <= 48*4^j gives tail width 48*2^-K/18 =", f"{48*2**-K/18:.4f})")
