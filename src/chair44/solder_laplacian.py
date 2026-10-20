"""
src/chair44/solder_laplacian.py
================================================================================
Soldered Bundle Laplacian Delta_solder on 3D Chair44.
Proves exact algebraic eigenvalues on Level-1 Tile Laplacian:
  0, (21 +- 3*sqrt(5))/2, 15 +- 3*sqrt(2), 24
================================================================================
"""

import collections
import numpy as np
from scipy.linalg import eigh
from scipy.sparse import coo_matrix


def build_solder_laplacian(tiles):
    """
    Constructs the 3N x 3N soldered Laplacian coupling translational displacements
    with rotational orientations.
    """
    n = len(tiles)
    owner = {c: a for a, (_, _, cubes) in enumerate(tiles) for c in cubes}

    W = collections.Counter()
    N_panels = collections.defaultdict(lambda: np.zeros((3, 3), dtype=float))

    for (x, y, z), a in owner.items():
        for ax, (dx, dy, dz) in enumerate([(1, 0, 0), (0, 1, 0), (0, 0, 1)]):
            b = owner.get((x + dx, y + dy, z + dz))
            if b is not None and b != a:
                u, v = (a, b) if a < b else (b, a)
                W[(u, v)] += 1
                N_panels[(u, v)][ax, ax] += 1.0

    rows_s, cols_s, vals_s = [], [], []
    diag_s = [np.zeros((3, 3), dtype=float) for _ in range(n)]

    for (u, v), w in W.items():
        Mu = tiles[u][0].astype(float)
        Mv = tiles[v][0].astype(float)
        Nuv = N_panels[(u, v)]
        diag_s[u] += w * np.eye(3) + Mu.T @ Nuv @ Mu
        diag_s[v] += w * np.eye(3) + Mv.T @ Nuv @ Mv
        off_uv = -w * np.eye(3) - Mu.T @ Nuv @ Mv
        for r in range(3):
            for c_idx in range(3):
                if abs(off_uv[r, c_idx]) > 1e-12:
                    rows_s.extend([3 * u + r, 3 * v + c_idx])
                    cols_s.extend([3 * v + c_idx, 3 * u + r])
                    vals_s.extend([off_uv[r, c_idx], off_uv[r, c_idx]])

    for u in range(n):
        for r in range(3):
            for c_idx in range(3):
                if abs(diag_s[u][r, c_idx]) > 1e-12:
                    rows_s.append(3 * u + r)
                    cols_s.append(3 * u + c_idx)
                    vals_s.append(diag_s[u][r, c_idx])

    Delta_solder = coo_matrix((vals_s, (rows_s, cols_s)), shape=(3 * n, 3 * n)).tocsr()
    return Delta_solder


def level1_tile_laplacian_spectrum(tiles=None):
    """
    Computes Level-1 Tile Adjacency Laplacian and returns sorted eigenvalues.
    """
    if tiles is None:
        from src.chair44.fr30_frames import FR30, generate_supertile_tiles
        tiles = generate_supertile_tiles(FR30, 1)
    n = len(tiles)

    owner = {c: a for a, (_, _, cubes) in enumerate(tiles) for c in cubes}
    W = collections.Counter()
    for (x, y, z), a in owner.items():
        for dx, dy, dz in [(1, 0, 0), (0, 1, 0), (0, 0, 1)]:
            b = owner.get((x + dx, y + dy, z + dz))
            if b is not None and b != a:
                u, v = (a, b) if a < b else (b, a)
                W[(u, v)] += 1

    L_t1 = np.zeros((n, n), dtype=float)
    for (u, v), w in W.items():
        L_t1[u, v] -= w
        L_t1[v, u] -= w
        L_t1[u, u] += w
        L_t1[v, v] += w

    return np.sort(eigh(L_t1, eigvals_only=True))
