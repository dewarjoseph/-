r"""
src/chair44/geometry.py
================================================================================
Geometric foundations of the 3D Chair44 (Q/R^44) monotile C_3 = [0,2]^3 \ (1,2]^3.
Constructs constituent unit cubes, boundary square panels, maximal flat facets,
and the rep-2^N doubled-coordinate hierarchical substitution dynamics.
Grounded in Tsiokos (2026), Flicker (arXiv:2609.23783v2), and Kamenetsky (arXiv:2610.00916v1).
================================================================================
"""

import itertools
import collections
from typing import List, Dict, Tuple, Set, Any
import numpy as np


# 7 child octant vectors U_3 = {0,1}^3 \ {(1,1,1)}
U3: List[Tuple[int, int, int]] = [
    v for v in itertools.product((0, 1), repeat=3) if v != (1, 1, 1)
]

# Base centers in doubled coordinates (2u + 1)
BASE_CENTERS: List[np.ndarray] = [
    np.array([2 * u[0] + 1, 2 * u[1] + 1, 2 * u[2] + 1], dtype=int) for u in U3
]


def get_chair_cubes() -> np.ndarray:
    r"""
    Returns the coordinates of the 7 unit cubes constituting the fundamental
    3D Chair monotile C_3 = [0,2]^3 \ (1,2]^3.
    Each cube is represented by its integer origin (x, y, z) in {0, 1}^3.
    
    Returns:
        np.ndarray of shape (7, 3), dtype=int
    """
    return np.array(U3, dtype=int)


def get_chair_faces() -> List[Dict[str, Any]]:
    """
    Constructs the 24 boundary square panels of the 3D Chair monotile C_3.
    Removes all internal shared faces between constituent unit cubes.
    
    Each boundary panel is characterized by:
      - 'origin': (x, y, z) corner coordinate
      - 'axis': normal axis (0 for x, 1 for y, 2 for z)
      - 'normal': unit normal vector pointing outward (+-1)
      - 'cube': coordinate of the originating unit cube
      - 'facet_type': 'outer' (on [0,2]^3 boundary) or 'inner' (on (1,2]^3 socket)
      
    Returns:
        List of 24 panel dictionaries.
    """
    cubes_set = set(U3)
    panels = []
    
    for c in U3:
        for ax in range(3):
            for sgn in (-1, 1):
                nb = list(c)
                nb[ax] += sgn
                if tuple(nb) not in cubes_set:
                    # Outer facing panel
                    n_vec = np.zeros(3, dtype=int)
                    n_vec[ax] = sgn
                    origin = list(c)
                    if sgn == 1:
                        origin[ax] += 1
                    
                    # Determine whether it's an outer bounding box face or inner socket face
                    # Outer bounding box faces are at x=0, y=0, z=0 (sgn=-1) or x=2, y=2, z=2 (sgn=+1)
                    is_outer = (c[ax] == 0 and sgn == -1) or (c[ax] == 1 and sgn == 1)
                    
                    panels.append({
                        "cube": c,
                        "origin": tuple(origin),
                        "axis": ax,
                        "normal": tuple(n_vec),
                        "facet_type": "outer" if is_outer else "inner"
                    })
                    
    return panels


def perm_mat(p: Tuple[int, int, int]) -> np.ndarray:
    """
    Converts a permutation tuple of (0, 1, 2) into a 3x3 orthogonal permutation matrix.
    """
    M = np.zeros((3, 3), dtype=int)
    for i in range(3):
        M[i, p[i]] = 1
    return M


def generate_supertile_tiles(frames_dict: Dict[Any, Tuple[int, int, int]], level: int) -> List[Tuple[np.ndarray, np.ndarray, Set[Tuple[int, int, int]]]]:
    """
    Generates the 8^level tiles of the Level-k Chair supertile using Kamenetsky's
    exact doubled-coordinate substitution (Section 6 of arXiv:2610.00916v1):
      (G, T) -> (G pi_0, 2T + G(1,1,1)) and (G D_s(v) pi_v, 2T + 4 G v) for v in U_3.
      
    Args:
        frames_dict: Mapping from '0' and v in U3 to permutation tuples pi_v in S_3.
        level: Recursion level k (produces 8^k tiles).
        
    Returns:
        List of (M_a, T_a, cubes_set) where:
          M_a is the 3x3 orientation matrix in SO(3),
          T_a is the 3D translation vector,
          cubes_set is the set of integer unit cube coordinates occupied by tile a.
    """
    child_ops = [(perm_mat(frames_dict['0']), np.array([1, 1, 1], dtype=int))]
    for v in U3:
        Ds = np.diag([1 - 2 * v[0], 1 - 2 * v[1], 1 - 2 * v[2]]).astype(int)
        child_ops.append((Ds @ perm_mat(frames_dict[v]), 4 * np.array(v, dtype=int)))

    poses = [(np.eye(3, dtype=int), np.array([0, 0, 0], dtype=int))]
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


def build_tile_adjacency(tiles: List[Tuple[np.ndarray, np.ndarray, Set[Tuple[int, int, int]]]]):
    """
    Computes contact adjacency between tiles in a supertile configuration.
    
    Returns:
        owner: dict mapping cube coordinate (x,y,z) to tile index a.
        W: Counter mapping tile pair (u, v) with u < v to shared square panel count.
        N_panels: dict mapping (u, v) to 3x3 normal projection matrix sum_f n_f n_f^T.
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
                e_ax = np.zeros((3, 3), dtype=float)
                e_ax[ax, ax] = 1.0
                N_panels[pair] += e_ax

    return owner, W, N_panels
