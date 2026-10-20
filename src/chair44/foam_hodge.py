"""
src/chair44/foam_hodge.py
================================================================================
Polyhedral Foam Hodge Laplacian on 3D Chair44.
Constructs boundary operators d0: C0 -> C1, d1: C1 -> C2 and evaluates
0-form and 1-form Hodge Laplacians:
  Delta_0 = d0^T d0
  Delta_1 = d0 d0^T + d1^T d1
================================================================================
"""

import collections
import numpy as np
from scipy.linalg import eigh
from scipy.sparse import coo_matrix


def build_chair_cell_complex(tiles):
    """
    Constructs the cell complex (0-cells/vertices, 1-cells/edges, 2-cells/faces)
    from the union of cubes in the tiling.
    """
    cubes_set = set()
    for _, _, cubes in tiles:
        cubes_set.update(cubes)

    # 0-cells: vertices (x, y, z) where x, y, z in Z
    V = set()
    # 1-cells: (v, axis) where axis in {0, 1, 2}
    E = set()
    # 2-cells: (v, normal_axis) where normal_axis in {0, 1, 2}
    F = set()

    for cx, cy, cz in cubes_set:
        for dx in (0, 1):
            for dy in (0, 1):
                for dz in (0, 1):
                    V.add((cx + dx, cy + dy, cz + dz))
        for dx in (0, 1):
            for dy in (0, 1):
                E.add(((cx, cy + dx, cz + dy), 0))
                E.add(((cx + dx, cy, cz + dy), 1))
                E.add(((cx + dx, cy + dy, cz), 2))
        for d in (0, 1):
            F.add(((cx + d, cy, cz), 0))
            F.add(((cx, cy + d, cz), 1))
            F.add(((cx, cy, cz + d), 2))

    return sorted(V), sorted(E), sorted(F)


def build_hodge_laplacian_0(V, E):
    """Constructs 0-form Hodge Laplacian Delta_0 = d0^T d0."""
    vi = {v: i for i, v in enumerate(V)}
    rows, cols, vals = [], [], []
    for idx_e, (v, ax) in enumerate(E):
        w = list(v)
        w[ax] += 1
        w = tuple(w)
        rows.extend([idx_e, idx_e])
        cols.extend([vi[v], vi[w]])
        vals.extend([-1.0, 1.0])

    d0 = coo_matrix((vals, (rows, cols)), shape=(len(E), len(V))).tocsr()
    Delta0 = d0.T @ d0
    return Delta0
