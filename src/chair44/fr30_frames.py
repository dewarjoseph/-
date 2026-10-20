"""
src/chair44/fr30_frames.py
================================================================================
Kamenetsky's Certified Homochiral Frame Assignment (FR30) and Control Sets.
Grounded in Kamenetsky (arXiv:2610.00916v1) and Tsiokos (2026).
================================================================================
"""

import itertools
import numpy as np

# Kamenetsky's certified FR30 frame assignment on U_3:
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

# Achiral control: all coordinate permutations trivial
ACHIRAL = {k: (0, 1, 2) for k in FR30}

# Canonical homochiral control (Kamenetsky Table 2)
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

U3 = [v for v in itertools.product((0, 1), repeat=3) if v != (1, 1, 1)]
BASE_CENTERS = [np.array([2 * u[0] + 1, 2 * u[1] + 1, 2 * u[2] + 1]) for u in U3]

SIGMA = [
    np.array([[0, 1], [1, 0]], dtype=complex),
    np.array([[0, -1j], [1j, 0]], dtype=complex),
    np.array([[1, 0], [0, -1]], dtype=complex),
]


def perm_mat(p):
    """Convert permutation tuple to 3x3 permutation matrix."""
    M = np.zeros((3, 3), dtype=int)
    for i in range(3):
        M[i, p[i]] = 1
    return M


def generate_supertile_tiles(frames_dict, level):
    """
    Generates 8^level tiles of the level-k Chair supertile using Kamenetsky's
    exact doubled-coordinate substitution:
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


def compute_p0_contact_poses(level=3):
    """
    Computes Kamenetsky's certified level-3 hierarchical contact poses P_0.
    Returns set of (rotation_matrix_tuple, translation_tuple) of size exactly 30.
    """
    tiles = generate_supertile_tiles(FR30, level)
    owner = {c: a for a, (_, _, cubes) in enumerate(tiles) for c in cubes}
    p0 = set()
    for (x, y, z), a in owner.items():
        for dx, dy, dz in [(1, 0, 0), (0, 1, 0), (0, 0, 1)]:
            b = owner.get((x + dx, y + dy, z + dz))
            if b is not None and b != a:
                for u, v in [(a, b), (b, a)]:
                    Gu, Tu, _ = tiles[u]
                    Gv, Tv, _ = tiles[v]
                    p0.add((tuple(map(tuple, Gu.T @ Gv)), tuple(Gu.T @ (Tv - Tu))))
    return p0


def count_contact_pairs_P0(frames_dict=FR30, level=3):
    """Returns the size of the initial contact language |P_0| (30)."""
    return len(compute_p0_contact_poses(level))

