"""
src/icosahedral_qc/lattice_bfs.py
================================================================================
Vectorized 6D -> 3D Cut-and-Project Engine via Breadth-First Search on Z^6.
Generates finite physical quasicrystal patches in E_parallel whose perpendicular
projection x_perp = P_perp n falls inside the acceptance polytope W subset E_perp.
================================================================================
"""

from typing import Tuple, Optional
import numpy as np
from scipy.spatial import ConvexHull
from src.icosahedral_qc.projectors import P_PAR, P_PERP
from src.icosahedral_qc.windows import get_acceptance_window


def bfs_vectorized_6d(hull: ConvexHull, R_max: float) -> Tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray]:
    """
    High-performance vectorized breadth-first search along unit edges of Z^6
    from the origin (0,0,0,0,0,0) selecting vertices satisfying:
      1. ||x_parallel(n)||_2 <= R_max
      2. x_perp(n) = P_perp n in hull.
      
    Args:
        hull: Acceptance polytope in E_perp (ConvexHull)
        R_max: Maximum physical space radius cutoff in E_parallel
        
    Returns:
        nodes: (N, 6) int64 hypercubic lattice vectors in Z^6
        x_par: (N, 3) float64 physical space coordinates in E_parallel
        x_perp: (N, 3) float64 perpendicular space coordinates in E_perp
        r_norms: (N,) float64 Euclidean radial distances in physical space.
    """
    A, b = hull.equations[:, :3], hull.equations[:, 3]
    AP = A @ P_PERP
    steps = np.vstack([np.eye(6, dtype=np.int64), -np.eye(6, dtype=np.int64)])
    weights = np.array([64 ** i for i in range(6)], dtype=np.int64)
    offset = 32

    frontier = np.zeros((1, 6), dtype=np.int64)
    visited_keys = np.array([np.sum((frontier[0] + offset) * weights)], dtype=np.int64)
    all_nodes = [frontier]
    R2 = (R_max + 1e-9) ** 2

    while len(frontier) > 0:
        cand = (frontier[:, None, :] + steps[None, :, :]).reshape(-1, 6)
        cand_keys = (cand + offset) @ weights
        u_keys, u_idx = np.unique(cand_keys, return_index=True)
        mask_new = ~np.isin(u_keys, visited_keys, assume_unique=True)
        cand = cand[u_idx[mask_new]]
        u_keys = u_keys[mask_new]
        if len(cand) == 0:
            break
        visited_keys = np.union1d(visited_keys, u_keys)
        cand_f = cand.astype(float)
        x_par = cand_f @ P_PAR.T
        mask_r = np.sum(x_par ** 2, axis=1) <= R2
        cand = cand[mask_r]
        cand_f = cand_f[mask_r]
        if len(cand) == 0:
            break
        mask_w = np.all(cand_f @ AP.T + b[None, :] <= 1e-9, axis=1)
        frontier = cand[mask_w]
        if len(frontier) > 0:
            all_nodes.append(frontier)

    nodes = np.vstack(all_nodes)
    nodes_f = nodes.astype(float)
    x_par_all = nodes_f @ P_PAR.T
    x_perp_all = nodes_f @ P_PERP.T
    r_norms = np.linalg.norm(x_par_all, axis=1)
    return nodes, x_par_all, x_perp_all, r_norms


def generate_quasicrystal_patch(radius: float, window_name: str = "W_b") -> np.ndarray:
    """
    Generates a physical space quasicrystal patch of specified radius and acceptance window.
    
    Args:
        radius: Physical radius cutoff R_max
        window_name: 'W_b' (chiral), '-W_b' (mirror), or 'W_a' (achiral)
        
    Returns:
        np.ndarray of shape (N, 3) containing 3D physical coordinates x_par.
    """
    hull = get_acceptance_window(window_name)
    _, x_par, _, _ = bfs_vectorized_6d(hull, radius)
    return x_par


def build_patch_adjacency(nodes: np.ndarray) -> np.ndarray:
    """
    Constructs the unweighted graph adjacency matrix A_{ij} for a finite patch
    where sites i and j are connected if and only if they differ by a unit step
    in Z^6: n_i - n_j in {+-e_alpha}_{alpha=0..5}.
    
    Returns:
        np.ndarray of shape (N, N), dtype=float.
    """
    N = len(nodes)
    weights = np.array([64 ** i for i in range(6)], dtype=np.int64)
    offset = 32
    keys = (nodes + offset) @ weights
    sort_idx = np.argsort(keys)
    sorted_keys = keys[sort_idx]

    adj = np.zeros((N, N), dtype=float)
    for ax in range(6):
        nb = nodes.copy()
        nb[:, ax] += 1
        nb_keys = (nb + offset) @ weights
        pos = np.searchsorted(sorted_keys, nb_keys)
        valid = pos < N
        pos_v = pos[valid]
        match = sorted_keys[pos_v] == nb_keys[valid]
        src = np.where(valid)[0][match]
        dst = sort_idx[pos_v[match]]
        adj[src, dst] = 1.0
        adj[dst, src] = 1.0
        
    return adj
