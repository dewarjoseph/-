"""
src/icosahedral_qc/windows.py
================================================================================
Perpendicular Space (E_perp) Acceptance Windows for 6D -> 3D Cut-and-Project:
  - W_a: Achiral canonical Rhombic Triacontahedron (RTH, symmetry I_h, order 120)
  - W_b: Chiral window = convex hull of 60-point proper icosahedral (I) orbit of seed
  - -W_b: Mirror enantiomer window (parity-inverted, breaks mirror planes in opposite sense).
================================================================================
"""

import itertools
from typing import Tuple, Dict, Any, Union
import numpy as np
from scipy.spatial import ConvexHull
from src.icosahedral_qc.projectors import P_PERP, compute_icosahedral_symmetry_groups

# Canonical generic chiral seed in E_perp (breaks all mirror planes of I_h)
P0_CHIRAL: np.ndarray = np.array([0.08, 0.25, 1.48], dtype=float)


def get_acceptance_windows(seed: np.ndarray = P0_CHIRAL) -> Tuple[ConvexHull, ConvexHull, ConvexHull]:
    """
    Returns the three fundamental acceptance windows as ConvexHull objects in E_perp:
      hull_a: Achiral Rhombic Triacontahedron (projected 6-cube [-0.5, 0.5]^6)
      hull_b: Chiral 60-point I-orbit window W_b
      hull_bm: Mirror enantiomer window -W_b.
    """
    _, _, _, R_perp_I = compute_icosahedral_symmetry_groups()

    # Window (a): projected 6-cube [-0.5, 0.5]^6 into E_perp
    cube6 = np.array(list(itertools.product((-0.5, 0.5), repeat=6)), dtype=float)
    hull_a = ConvexHull((P_PERP @ cube6.T).T)

    # Window (b): 60-point orbit of chiral seed under proper rotations I
    orbit_b = np.array([R @ seed for R in R_perp_I])
    hull_b = ConvexHull(orbit_b)

    # Window (-b): mirror enantiomer via parity inversion
    orbit_bm = np.array([-R @ seed for R in R_perp_I])
    hull_bm = ConvexHull(orbit_bm)

    return hull_a, hull_b, hull_bm


def get_acceptance_window(name: str, seed: np.ndarray = P0_CHIRAL) -> ConvexHull:
    """
    Retrieves an acceptance window by name:
      'W_a' or 'a': Achiral rhombic triacontahedron
      'W_b' or 'b': Chiral 60-point window
      '-W_b' or '-b' or 'mirror': Mirror enantiomer window.
    """
    hull_a, hull_b, hull_bm = get_acceptance_windows(seed=seed)
    key = name.strip()
    if key in ("W_a", "a", "achiral"):
        return hull_a
    elif key in ("W_b", "b", "chiral"):
        return hull_b
    elif key in ("-W_b", "-b", "mirror", "W_b_mirror"):
        return hull_bm
    else:
        raise ValueError(f"Unknown acceptance window name: {name}. Expected 'W_a', 'W_b', or '-W_b'.")


def build_acceptance_windows(seed: np.ndarray = P0_CHIRAL) -> Tuple[ConvexHull, ConvexHull, ConvexHull]:
    """Compatibility alias for existing imports."""
    return get_acceptance_windows(seed=seed)
