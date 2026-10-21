"""
Level-5 canonical plaquette curvature frequencies (32768 tiles, 229376 cubes).
Run from the repository root:  python3 -I audit/plaquette_curvature_level5.py   (a few minutes)
"""
import os, sys, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
from independent_clifford_q8_audit import FR30, tiles_at_level, panel_edges, clifford_link, q8label

lvl = int(sys.argv[1]) if len(sys.argv) > 1 else 5
tiles = tiles_at_level(FR30, lvl); owner, edges = panel_edges(tiles); cubes = set(owner)
cache = {}
def link_cubes(c1, c2):
    a, b = owner[c1], owner[c2]
    if a == b: return None
    d = (c2[0]-c1[0], c2[1]-c1[1], c2[2]-c1[2]); key = (a, b, d)
    if key not in cache: cache[key] = clifford_link(tiles[a][0], tiles[b][0], np.array(d, int))
    return cache[key]
cnt = collections.Counter(); mixed = 0; total = 0; E = np.eye(2, dtype=complex)
for c in cubes:
    for (i, j) in [(0, 1), (1, 2), (0, 2)]:
        ei = [0, 0, 0]; ei[i] = 1; ej = [0, 0, 0]; ej[j] = 1
        c1 = (c[0]+ei[0], c[1]+ei[1], c[2]+ei[2]); c2 = (c1[0]+ej[0], c1[1]+ej[1], c1[2]+ej[2]); c3 = (c[0]+ej[0], c[1]+ej[1], c[2]+ej[2])
        if c1 in cubes and c2 in cubes and c3 in cubes:
            total += 1
            if len({owner[c], owner[c1], owner[c2], owner[c3]}) > 1:
                mixed += 1; W = E
                for x, y in ((c, c1), (c1, c2), (c2, c3), (c3, c)):
                    L = link_cubes(x, y)
                    if L is not None: W = W @ L
                cnt[q8label(W)] += 1
nontriv = mixed - cnt['+1']; tr0 = sum(v for k, v in cnt.items() if k not in ('+1', '-1'))
print(f"level {lvl}: plaquettes={total} inter-tile={mixed} dist={dict(cnt)}")
print(f"  nontrivial={100*nontriv/mixed:.2f}%  Tr=0: {100*tr0/mixed:.2f}%  W=-1: {100*cnt['-1']/mixed:.2f}%")
