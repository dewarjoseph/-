r"""
src/chair44/periodic_crystal.py
================================================================================
Exact Pure-Translation Periodic 3D Chair Crystal on the Index-7 Lattice
Lambda_7 = Ker(x + 2y + 4z mod 7) and Rotated-Cell Periodic Controls.
Grounded in explore_breakthroughs.py and Kamenetsky (2026).

Theorem:
  The homomorphism phi(x,y,z) = (x + 2y + 4z) mod 7 maps the 7 constituent cubes
  U_3 = {0,1}^3 \ {(1,1,1)} bijectively onto Z_7 = {0, 1, 2, 3, 4, 5, 6}.
  Because (U_3 - U_3) intersect Lambda_7 = {0}, translating C_3 along
  the index-7 lattice Lambda_7 with basis
    b1 = (1, 1, 1),  b2 = (2, 1, -1),  b3 = (-1, 2, 1)  (det = 7)
  tiles R^3 periodically with zero rotations and zero gaps or overlaps.
================================================================================
"""

import itertools
from typing import List, Tuple, Set, Any
import numpy as np
from src.chair44.geometry import U3, generate_supertile_tiles


def homomorphic_map(x: int, y: int, z: int) -> int:
    """
    Computes the canonical Z_7 homomorphism:
      phi(x, y, z) = (x + 2y + 4z) mod 7.
    Maps U_3 bijectively onto {0, 1, 2, 3, 4, 5, 6}.
    """
    return (x + 2 * y + 4 * z) % 7


def get_lambda7_basis() -> np.ndarray:
    """
    Returns the primitive basis vectors for the index-7 translation lattice Lambda_7:
      b1 = (1, 1, 1)
      b2 = (2, 1, -1)
      b3 = (-1, 2, 1)
    with det = +7.
    
    Returns:
        np.ndarray of shape (3, 3) where rows are b1, b2, b3.
    """
    return np.array([
        [1, 1, 1],
        [2, 1, -1],
        [-1, 2, 1]
    ], dtype=int)


def generate_lambda7_periodic_chairs(level: int) -> List[Tuple[np.ndarray, np.ndarray, Set[Tuple[int, int, int]]]]:
    """
    Constructs the periodic 3D Chair crystal translating C_3 along Lambda_7:
      b1 = (1, 1, 1), b2 = (2, 1, -1), b3 = (-1, 2, 1)  (det = 7).
    Generates (2^level)^3 = 8^level tiles filling a periodic parallelepiped.
    
    Returns:
        List of (M_a, T_a, cubes_set) where M_a = I_3 for all tiles (pure translation).
    """
    basis = get_lambda7_basis()
    b1, b2, b3 = basis[0], basis[1], basis[2]
    L = 2 ** level
    tiles = []
    
    for i, j, k_idx in itertools.product(range(L), repeat=3):
        t = i * b1 + j * b2 + k_idx * b3
        cubes = {tuple(t + np.array(u, dtype=int)) for u in U3}
        tiles.append((np.eye(3, dtype=int), t, cubes))
        
    return tiles


def generate_rotated_cell_periodic(frames_dict: Any, k: int) -> List[Tuple[np.ndarray, np.ndarray, Set[Tuple[int, int, int]]]]:
    """
    Constructs the rotated-cell periodic control of 8 Level-k superchairs packed along
    the 2^k * Lambda_7 lattice.
    
    Returns:
        List of (M_a, T_a, cubes_set).
    """
    base_tiles = generate_supertile_tiles(frames_dict, k)
    basis = get_lambda7_basis()
    b1, b2, b3 = basis[0], basis[1], basis[2]
    scale = 2 ** k
    tiles = []
    
    for i1, i2, i3 in itertools.product((0, 1), repeat=3):
        shift = scale * (i1 * b1 + i2 * b2 + i3 * b3)
        sh_t = (int(shift[0]), int(shift[1]), int(shift[2]))
        for G, T, cubes in base_tiles:
            new_cubes = {(c[0] + sh_t[0], c[1] + sh_t[1], c[2] + sh_t[2]) for c in cubes}
            tiles.append((G, T + shift, new_cubes))
            
    return tiles
