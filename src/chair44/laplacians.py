"""
src/chair44/laplacians.py
================================================================================
Bimodal Soldered Laplacian L_solder = L_proto + M^T L_normal M and Level-1
Tile Adjacency Laplacian Exact Algebraic Eigenvalues.
Grounded in Tsiokos (2026), Flicker (2026), and Kamenetsky (2026).

Theorem 2:
  L_proto couples identical prototile body-axis channels across shared panels.
  L_normal couples normal flux n_f . phi across shared panels.
  Because M_a varies across tiles, [L_proto, L_normal] != 0, lifting all gauge
  degeneracies and resolving the coboundary gauge trap.

Exact Algebraic Spectrum of Level-1 Tile Laplacian (8x8):
  Spec(L_tile,1) = { 0, (21 +- 3*sqrt(5))/2, 15 +- 3*sqrt(2), 24 }
================================================================================
"""

import collections
from typing import List, Tuple, Dict, Any
import numpy as np
from scipy.linalg import eigh
from src.chair44.geometry import generate_supertile_tiles
from src.chair44.frames import FR30


def build_soldered_laplacian(tiles: List[Tuple[np.ndarray, np.ndarray, Any]], use_abs_frames: bool = False) -> Tuple[np.ndarray, np.ndarray, np.ndarray]:
    """
    Constructs the 3N x 3N bimodal soldered Laplacian:
      L_solder = L_proto + L_normal
    where:
      L_proto = L_0 x I_3 (body-axis continuity),
      L_normal couples normal flux n_f . phi across shared panels:
        diagonal block a: M_a^T N_ab M_a
        off-diagonal block (a, b): -M_a^T N_ab M_b.
        
    Returns:
        (L_solder, L_proto, L_normal) as 3N x 3N numpy arrays.
    """
    n = len(tiles)
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

    L_proto = np.zeros((3 * n, 3 * n), dtype=float)
    L_normal = np.zeros((3 * n, 3 * n), dtype=float)

    for (a, b), w in W.items():
        Ma = np.abs(tiles[a][0]).astype(float) if use_abs_frames else tiles[a][0].astype(float)
        Mb = np.abs(tiles[b][0]).astype(float) if use_abs_frames else tiles[b][0].astype(float)
        Nab = N_panels[(a, b)]

        # L_proto couples body axes
        L_proto[3 * a : 3 * a + 3, 3 * b : 3 * b + 3] -= w * np.eye(3)
        L_proto[3 * b : 3 * b + 3, 3 * a : 3 * a + 3] -= w * np.eye(3)
        L_proto[3 * a : 3 * a + 3, 3 * a : 3 * a + 3] += w * np.eye(3)
        L_proto[3 * b : 3 * b + 3, 3 * b : 3 * b + 3] += w * np.eye(3)

        # L_normal couples spatial normal flux
        L_normal[3 * a : 3 * a + 3, 3 * a : 3 * a + 3] += Ma.T @ Nab @ Ma
        L_normal[3 * b : 3 * b + 3, 3 * b : 3 * b + 3] += Mb.T @ Nab @ Mb
        L_normal[3 * a : 3 * a + 3, 3 * b : 3 * b + 3] -= Ma.T @ Nab @ Mb
        L_normal[3 * b : 3 * b + 3, 3 * a : 3 * a + 3] -= Mb.T @ Nab @ Ma

    L_solder = L_proto + L_normal
    return L_solder, L_proto, L_normal


def analyze_soldered_laplacian(tiles: List[Tuple[np.ndarray, np.ndarray, Any]], use_abs_frames: bool = False) -> Tuple[np.ndarray, float]:
    """
    Computes real eigenvalues of L_solder and the Frobenius commutator norm
      ||[L_proto, L_normal]||_F.
    """
    L_solder, L_proto, L_normal = build_soldered_laplacian(tiles, use_abs_frames=use_abs_frames)
    ev = np.sort(eigh(L_solder, eigvals_only=True))
    comm_norm = float(np.linalg.norm(L_proto @ L_normal - L_normal @ L_proto))
    return ev, comm_norm


def build_level1_tile_laplacian() -> np.ndarray:
    """
    Builds the 8x8 scalar adjacency Laplacian for the 8 Level-1 tiles of Chair44.
    Weights correspond to shared square panels between tiles.
    """
    tiles = generate_supertile_tiles(FR30, 1)
    owner = {c: a for a, (_, _, cubes) in enumerate(tiles) for c in cubes}
    weights: Dict[Tuple[int, int], int] = {}
    
    for (x, y, z), a in owner.items():
        for dx, dy, dz in [(1, 0, 0), (0, 1, 0), (0, 0, 1)]:
            b = owner.get((x + dx, y + dy, z + dz))
            if b is not None and b != a:
                pair = (min(a, b), max(a, b))
                weights[pair] = weights.get(pair, 0) + 1

    L = np.zeros((8, 8), dtype=float)
    for (a, b), w in weights.items():
        L[a, b] -= w
        L[b, a] -= w
        L[a, a] += w
        L[b, b] += w
        
    return L


def compute_exact_level1_eigenvalues() -> Tuple[np.ndarray, np.ndarray, float]:
    """
    Calculates numerical eigenvalues of Level-1 tile Laplacian and compares with
    exact closed-form algebraic roots:
      0, (21 - 3*sqrt(5))/2 (x2), 15 - 3*sqrt(2), (21 + 3*sqrt(5))/2 (x2), 15 + 3*sqrt(2), 24.
      
    Returns:
        (computed_evals, exact_evals, max_error)
    """
    L = build_level1_tile_laplacian()
    computed_evals = np.sort(eigh(L, eigvals_only=True))
    exact_evals = np.sort([
        0.0,
        (21.0 - 3.0 * np.sqrt(5.0)) / 2.0,
        (21.0 - 3.0 * np.sqrt(5.0)) / 2.0,
        15.0 - 3.0 * np.sqrt(2.0),
        (21.0 + 3.0 * np.sqrt(5.0)) / 2.0,
        (21.0 + 3.0 * np.sqrt(5.0)) / 2.0,
        15.0 + 3.0 * np.sqrt(2.0),
        24.0,
    ])
    max_err = float(np.max(np.abs(computed_evals - exact_evals)))
    return computed_evals, exact_evals, max_err


def compute_level1_tile_laplacian() -> Dict[str, Any]:
    """Compatibility helper returning verification dictionary."""
    computed_evals, exact_evals, max_err = compute_exact_level1_eigenvalues()
    return {
        "eigenvalues": computed_evals.tolist(),
        "exact_targets": exact_evals.tolist(),
        "max_err": max_err,
        "passed": bool(max_err < 1e-12)
    }
