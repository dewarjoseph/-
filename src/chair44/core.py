"""
src/chair44/core.py
================================================================================
Core Definitions for 3D Chair44 (Q/R^44) Aperiodic Monotile and Hierarchical
Substitution Dynamics Grounded in Tsiokos (2026) and Kamenetsky (2026).
================================================================================
"""

import collections
import itertools
import numpy as np

# Kamenetsky's Certified Homochiral Frame Assignment (FR30)
FR30 = {
    '0': (0, 1, 2),
    (0, 0, 0): (0, 1, 2),
    (0, 0, 1): (0, 2, 1),
    (0, 1, 0): (2, 1, 0),
    (0, 1, 1): (1, 2, 0),
    (1, 0, 0): (1, 0, 2),
    (1, 0, 1): (0, 1, 2),
    (1, 1, 0): (2, 0, 1),
}

# Achiral Control: All coordinate permutations trivial
ACHIRAL = {k: (0, 1, 2) for k in FR30}

# Canonical Homochiral Control (Kamenetsky Table 2)
CANONICAL_HOMO = {
    '0': (0, 1, 2),
    (0, 0, 0): (0, 1, 2),
    (0, 0, 1): (0, 2, 1),
    (0, 1, 0): (0, 2, 1),
    (0, 1, 1): (0, 1, 2),
    (1, 0, 0): (0, 2, 1),
    (1, 0, 1): (0, 1, 2),
    (1, 1, 0): (0, 1, 2),
}

# 7 child octant vectors U_3 = {0,1}^3 \ {(1,1,1)}
U3 = [v for v in itertools.product((0, 1), repeat=3) if v != (1, 1, 1)]
BASE_CENTERS = [np.array([2 * u[0] + 1, 2 * u[1] + 1, 2 * u[2] + 1]) for u in U3]

# Pauli Spin Matrices in SU(2)
SIGMA = [
    np.array([[0, 1], [1, 0]], dtype=complex),
    np.array([[0, -1j], [1j, 0]], dtype=complex),
    np.array([[1, 0], [0, -1]], dtype=complex),
]


def perm_mat(p):
    """Converts a 3-element permutation tuple into a 3x3 permutation matrix."""
    M = np.zeros((3, 3), dtype=int)
    for i in range(3):
        M[i, p[i]] = 1
    return M


def generate_supertile_tiles(frames_dict, level):
    """
    Generates the 8^level tiles of the level-k Chair supertile using Kamenetsky's
    exact doubled-coordinate substitution (Section 6 of arXiv:2610.00916v1):
      (G, T) -> (G pi_0, 2T + G(1,1,1)) and (G D_s(v) pi_v, 2T + 4 G v) for v in U_3.
    Returns list of (M_a, T_a, set_of_unit_cube_coords).
    """
    child_ops = [(perm_mat(frames_dict['0']), np.array([1, 1, 1]))]
    for v in U3:
        Ds = np.diag([1 - 2 * v[0], 1 - 2 * v[1], 1 - 2 * v[2]])
        child_ops.append((Ds @ perm_mat(frames_dict[v]), 4 * np.array(v)))

    poses = [(np.eye(3, dtype=int), np.array([0, 0, 0]))]
    for _ in range(level):
        new_poses = []
        for G, T in poses:
            for gc, tc in child_ops:
                new_poses.append((G @ gc, 2 * T + G @ tc))
        poses = new_poses

    tiles = []
    for G, T in poses:
        cubes = {tuple((G @ bc + 2 * T - 1) // 2) for bc in BASE_CENTERS}
        tiles.append((G, T, cubes))
    return tiles


def build_tile_adjacency(tiles):
    """
    Computes shared panel counts W[(a, b)] and normal projection matrices N_panels[(a, b)].
    """
    owner = {}
    for a, (_, _, cubes) in enumerate(tiles):
        for c in cubes:
            owner[c] = a

    N_panels = collections.defaultdict(lambda: np.zeros((3, 3), dtype=float))
    W = collections.Counter()
    for (x, y, z), a in owner.items():
        for ax, (dx, dy, dz) in enumerate([(1, 0, 0), (0, 1, 0), (0, 0, 1)]):
            b = owner.get((x + dx, y + dy, z + dz))
            if b is not None and b != a:
                pair = (min(a, b), max(a, b))
                W[pair] += 1
                e_ax = np.zeros((3, 3))
                e_ax[ax, ax] = 1.0
                N_panels[pair] += e_ax

    return owner, W, N_panels
