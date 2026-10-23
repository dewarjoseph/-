#!/usr/bin/env python3
"""Phase VII (exploratory): does a legal R-star type determine the centre tile's role in its parent (child index and parent pose
relative to the tile)?  If yes at radius R, every tiling whose R-stars are legal decomposes uniquely into level-1 supertiles
(the whole level-1 supertile lies inside the 1-star) [CORRECTION, Phase VII-B: this parenthesis is false -- children (2,7), (3,6),
(4,5) are at Chebyshev distance 2; the decomposition is recovered via the centre child, see PHASE7_REPORT.md E7 and section 6],
the first step of a local-rules argument.  Census over all complete
R-stars of T_6.  Usage: python -u -I audit/phase7_recognizability.py -> audit/results/phase7_recognizability.json"""
import os, sys, json, collections
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); RES = os.path.join(HERE, 'results')
import numpy as np
import phase7_local as P
G, T = P.gen_poses(6); grid = P.owner_grid(6, G, T); n = len(G); fi = P.frame_index(G)
Gp, Tp = P.gen_poses(5); fip = P.frame_index(Gp)
out = {}
for R in (1, 2):
    roles = collections.defaultdict(set); odd = P.LODD[R]
    for s in range(0, n, 4096):
        sl = slice(s, min(n, s + 4096)); O = P.lookup(grid, P.cubes_of_poses(G[sl], T[sl], odd)); comp = (O >= 0).all(1)
        for i in np.nonzero(comp)[0]:
            a = s + i; Oa = O[i]; rf = P.MULT[P.INV[fi[a]], fi[Oa]]
            rel = np.asarray(G[a], np.int64).T @ (T[Oa] - T[a]).T
            k = frozenset(int(x) for x in P.encode(rf, rel.T))
            par = a // 8; child = a % 8
            prel = P.MULT[P.INV[fi[a]], fip[par]]; ptr = tuple(int(x) for x in np.asarray(G[a], np.int64).T @ (2 * Tp[par] - T[a]))
            roles[k].add((child, int(prel), ptr))
    amb = {len(v) for v in roles.values()}
    out[R] = {'types': len(roles), 'max_roles_per_type': max(amb), 'ambiguous_types': sum(1 for v in roles.values() if len(v) > 1)}
    print(R, out[R], flush=True)
json.dump(out, open(os.path.join(RES, 'phase7_recognizability.json'), 'w'), indent=1)
