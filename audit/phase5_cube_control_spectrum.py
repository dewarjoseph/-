"""
Alternative-substitution control for the experimental proposal: the unit-cube block substitution (periodic cubic
geometry) carrying the FR30-type frame decoration and the same Clifford Q8 rule.  Lowest eigenvalues of the hopping
operator with free and pinned boundaries at levels 2-4, plus the mirror-reflected FR30 chair spectrum check.
Run from the repository root:  python3 -I audit/phase5_cube_control_spectrum.py
"""
import os, sys, itertools, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np, scipy.sparse as sps, scipy.sparse.linalg as spl
from independent_clifford_q8_audit import U3, FR30, perm_mat, tiles_at_level, panel_edges, clifford_link
V8 = list(itertools.product((0, 1), repeat=3)); dec = {v: FR30.get(v, (0, 2, 1)) for v in V8}
def cube_tiles(level):
    ops = [(np.diag([1-2*v[0], 1-2*v[1], 1-2*v[2]]) @ perm_mat(dec[v]), 2*np.array(v)) for v in V8]
    poses = [(np.eye(3, dtype=int), np.zeros(3, dtype=int))]
    for _ in range(level): poses = [(G @ g, 2*T + G @ t) for G, T in poses for g, t in ops]
    return [(G, T, frozenset([tuple((G @ np.array([1, 1, 1]) + 2*T - 1) // 2)])) for G, T in poses]
def spectrum(tiles, pinned, k=4):
    owner, edges = panel_edges(tiles); n = len(tiles); deg = collections.Counter()
    for a, b, _, _, _ in edges: deg[a] += 1; deg[b] += 1
    bulk = max(deg.values()); rows, cols, vals = [], [], []
    for a in range(n):
        d = float(bulk) if pinned else float(deg[a])
        for r in range(2): rows.append(2*a+r); cols.append(2*a+r); vals.append(d)
    for (a, b, nf, _, _) in edges:
        C = clifford_link(tiles[a][0], tiles[b][0], nf)
        for r in range(2):
            for c in range(2): rows += [2*a+r, 2*b+c]; cols += [2*b+c, 2*a+r]; vals += [-C[r, c], -np.conj(C[r, c])]
    H = sps.coo_matrix((vals, (rows, cols)), shape=(2*n, 2*n)).tocsr()
    if 2*n <= 2048: w = np.linalg.eigvalsh(H.toarray())[:k]
    else: w = np.sort(spl.eigsh(H, k=k, sigma=-1.0 if not pinned else 0.0, which='LM', return_eigenvectors=False))
    return w, bulk, len(edges)
for lvl in (2, 3, 4):
    t = cube_tiles(lvl)
    for pinned in (False, True):
        w, bulk, ne = spectrum(t, pinned)
        print(f"unit-cube/FR30-type level {lvl}: tiles={len(t)} panels={ne} bulk degree={bulk} {'pinned' if pinned else 'free  '} lowest={np.round(w,5)}")
# mirror-reflected FR30 chair: identical spectrum (gauge equivalence), levels 2-3
P = np.diag([-1, 1, 1])
for lvl in (2, 3):
    tiles = tiles_at_level(FR30, lvl)
    tilesP = [(P @ G @ P, P @ T, frozenset((-c[0]-1, c[1], c[2]) for c in cs)) for G, T, cs in tiles]
    w1, _, _ = spectrum(tiles, False, 6); w2, _, _ = spectrum(tilesP, False, 6)
    print(f"mirror test level {lvl}: FR30 lowest {np.round(w1,6)} ; mirrored {np.round(w2,6)} ; max|diff|={np.abs(w1-w2).max():.2e}")
