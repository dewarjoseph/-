#!/usr/bin/env python3
"""Phase VII-B (C): independent reconstruction of the legal R-star type counts |V_R| = 72, 165, 445, 762 (R = 1..4).

Census side (independent code): tiles from independent_clifford_q8_audit.tiles_at_level(FR30, 6); the R-star of t is computed
from its definition -- every tile owning a cube at Chebyshev distance <= R from SOME cube of t -- by explicit distance tests
(no phase7_local.Lr offsets), restricted to tiles whose whole star region lies inside T_6; a type is the set of raw relative
poses (G_t^T G_b as a 3x3 tuple, G_t^T (T_b - T_t)).
Generator side (phase7_local): V_1 = forward Phi-orbit, V_2 = Phi_2(V_1), V_3 = Phi_3(V_2), V_4 = Phi_4(V_2); every
application asserts the closure-lemma instance.  The two sets are compared after converting the census keys to the
phase7_local encoding.  Completeness of the generated sets (every legal star is generated) is proved in the report, 6.1.
Usage: python -u -I audit/phase7b_census.py -> audit/results/phase7b_census.json"""
import os, sys, json, time, itertools
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); RES = os.path.join(HERE, 'results')
import numpy as np
from independent_clifford_q8_audit import FR30, tiles_at_level
T0 = time.time()
def log(*a): print(f"[{time.time()-T0:6.0f}s]", *a, flush=True)

def census(level=6, Rs=(1, 2, 3, 4)):
    tl = tiles_at_level(FR30, level); n = len(tl); N = 2 ** (level + 1)
    G = np.array([t[0] for t in tl]); T = np.array([t[1] for t in tl]); C = np.array([sorted(t[2]) for t in tl])     # (n, 7, 3)
    grid = np.full((N, N, N), -1, np.int64)
    for a in range(n): grid[C[a, :, 0], C[a, :, 1], C[a, :, 2]] = a
    out = {}
    for R in Rs:
        t0 = time.time(); types = set(); complete = 0
        box = np.array(list(itertools.product(range(-R, R + 2), repeat=3)))           # offsets from the block corner (superset)
        for s in range(0, n, 512):
            sl = slice(s, min(n, s + 512)); lo = C[sl].min(1)                         # (m, 3) block corner of each chair
            P = lo[:, None, :] + box[None]                                             # (m, B, 3) candidate cubes
            d = np.abs(P[:, :, None, :] - C[sl][:, None, :, :]).max(-1).min(-1)        # Chebyshev distance to the chair
            inside = ((P >= 0) & (P < N)).all(-1)
            for i in range(P.shape[0]):
                sel = d[i] <= R
                if not inside[i][sel].all(): continue
                own = grid[P[i][sel][:, 0], P[i][sel][:, 1], P[i][sel][:, 2]]
                if (own < 0).any(): continue
                complete += 1; a = s + i; Ga = G[a]
                types.add(frozenset((tuple((Ga.T @ G[b]).ravel()), tuple(Ga.T @ (T[b] - T[a]))) for b in set(own.tolist())))
        out[R] = (types, complete); log(f"census R={R}: {complete} complete stars, {len(types)} types ({time.time()-t0:.0f}s)")
    return out

if __name__ == '__main__':
    import phase7_local as P
    cen = census()
    G4, T4 = P.gen_poses(4); grid4 = P.owner_grid(4, G4, T4); cnt1, _ = P.star_types(G4, T4, grid4, P.LODD[1])
    seed = max(cnt1, key=cnt1.get); V = {1: {seed}}; fr = [seed]
    while fr:
        new = {kk for k in fr for kk in P.Phi_r(k, P.LODD[1]) if kk not in V[1]}; V[1] |= new; fr = list(new)
    V[2] = {kk for k in V[1] for kk in P.Phi_r(k, P.LODD[2])}; V[3] = {kk for k in V[2] for kk in P.Phi_r(k, P.LODD[3])}
    V[4] = {kk for k in V[2] for kk in P.Phi_r(k, P.LODD[4])}
    def conv(t): return frozenset(int(P.encode(P.gidx[g], np.array(r))) for g, r in t)
    out = {'types': {}, 'complete_stars': {}, 'generated': {}, 'equal_to_phase7_local': {}}
    for R in (1, 2, 3, 4):
        types, comp = cen[R]; conv_types = {conv(t) for t in types}
        out['types'][R] = len(types); out['complete_stars'][R] = comp; out['generated'][R] = len(V[R]); out['equal_to_phase7_local'][R] = conv_types == V[R]
        log(f"R={R}: census {len(types)} types, generated {len(V[R])}, equal: {conv_types == V[R]}")
    json.dump(out, open(os.path.join(RES, 'phase7b_census.json'), 'w'), indent=1)
