"""
src/chair44/laplacian.py
================================================================================
Bimodal Soldered Hodge-Laplacian L_solder and Exact Algebraic Eigenvalue Spectrum
of Level-1 Tile Adjacency.
================================================================================
"""

import numpy as np
from scipy.linalg import eigh
from src.chair44.core import build_tile_adjacency, generate_supertile_tiles, FR30


def analyze_soldered_laplacian(tiles, use_abs_frames=False, use_identity_frames=False):
    """
    Constructs L_solder = L_proto + L_normal and calculates commutator norm
    || [L_proto, L_normal] ||_F and spectrum.
    """
    n = len(tiles)
    owner, W, N_panels = build_tile_adjacency(tiles)

    L_proto = np.zeros((3 * n, 3 * n))
    L_normal = np.zeros((3 * n, 3 * n))

    for (a, b), w in W.items():
        if use_identity_frames:
            Ma = np.eye(3)
            Mb = np.eye(3)
        elif use_abs_frames:
            Ma = np.abs(tiles[a][0]).astype(float)
            Mb = np.abs(tiles[b][0]).astype(float)
        else:
            Ma = tiles[a][0].astype(float)
            Mb = tiles[b][0].astype(float)

        Nab = N_panels[(a, b)]

        L_proto[3 * a : 3 * a + 3, 3 * b : 3 * b + 3] -= w * np.eye(3)
        L_proto[3 * b : 3 * b + 3, 3 * a : 3 * a + 3] -= w * np.eye(3)
        L_proto[3 * a : 3 * a + 3, 3 * a : 3 * a + 3] += w * np.eye(3)
        L_proto[3 * b : 3 * b + 3, 3 * b : 3 * b + 3] += w * np.eye(3)

        L_normal[3 * a : 3 * a + 3, 3 * a : 3 * a + 3] += Ma.T @ Nab @ Ma
        L_normal[3 * b : 3 * b + 3, 3 * b : 3 * b + 3] += Mb.T @ Nab @ Mb
        L_normal[3 * a : 3 * a + 3, 3 * b : 3 * b + 3] -= Ma.T @ Nab @ Mb
        L_normal[3 * b : 3 * b + 3, 3 * a : 3 * a + 3] -= Mb.T @ Nab @ Ma

    L_solder = L_proto + L_normal
    ev = np.sort(eigh(L_solder, eigvals_only=True))
    comm_norm = float(np.linalg.norm(L_proto @ L_normal - L_normal @ L_proto))
    return ev, comm_norm


def compute_level1_tile_laplacian():
    """
    Computes Level-1 Tile-Adjacency Laplacian eigenvalues and verifies the exact
    algebraic formula:
      0, (21 +- 3*sqrt(5))/2 (mult 2), 15 +- 3*sqrt(2) (mult 1), 24 (mult 1).
    """
    tiles = generate_supertile_tiles(FR30, 1)
    owner, W, _ = build_tile_adjacency(tiles)
    Lt1 = np.zeros((8, 8))
    for (a, b), w in W.items():
        Lt1[a, b] = Lt1[b, a] = -w
        Lt1[a, a] += w
        Lt1[b, b] += w
    ev_t1 = np.sort(eigh(Lt1, eigvals_only=True))
    exact_t1 = np.sort([
        0.0,
        (21 - 3 * np.sqrt(5)) / 2,
        (21 - 3 * np.sqrt(5)) / 2,
        15 - 3 * np.sqrt(2),
        (21 + 3 * np.sqrt(5)) / 2,
        (21 + 3 * np.sqrt(5)) / 2,
        15 + 3 * np.sqrt(2),
        24.0,
    ])
    max_err = float(np.max(np.abs(ev_t1 - exact_t1)))
    return {
        "ev_t1": ev_t1.tolist(),
        "exact_t1": exact_t1.tolist(),
        "max_err": max_err,
        "passed": bool(max_err < 1e-12)
    }
