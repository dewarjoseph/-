"""
src/icosahedral_qc/cut_and_project.py
================================================================================
Vectorized 6D -> 3D Cut-and-Project Algorithm Generating Quasicrystal Patches.
================================================================================
"""

import numpy as np
from src.icosahedral_qc.projector import P_PAR, P_PERP


def generate_patch_bfs(hull, R_max):
    """
    Vectorized Breadth-First Search along unit edges of Z^6 from origin
    up to ||x_par|| <= R_max whose perpendicular projection falls inside hull.
    Returns:
      nodes: (N, 6) int64 lattice vectors in Z^6
      x_par: (N, 3) float64 physical space coordinates in E_parallel
      x_perp: (N, 3) float64 internal space coordinates in E_perp
      r_norms: (N,) float64 radial distances in physical space
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
