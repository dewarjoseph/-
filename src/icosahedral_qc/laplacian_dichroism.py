"""
src/icosahedral_qc/laplacian_dichroism.py
================================================================================
Dynamical Graph-Laplacian Circular-Polarization Wave Probe D_lap(R).
Evaluates the transition amplitude of wave |k_2> scattering off the quasicrystal
graph Laplacian into <-k_1|:
  M_12^(L) = <-k_1 | L | k_2> = sum_{alpha=0}^5 (1 - e^{i k_1 . d_alpha})(1 - e^{i k_2 . d_alpha}) F_alpha(k_3)*
Interfering with Born amplitude A_12 = F(k_1) F(k_2) in Left (-i) vs Right (+i)
circular quadrature gives:
  J_L = |A_12 - i M_12^(L)|^2,  J_R = |A_12 + i M_12^(L)|^2
  Delta J_LR = J_L - J_R = 4 Im[ A_12 conj(M_12^(L)) ]
  D_lap = sum |Delta J_LR| / (4 sum |A_12| |M_12^(L)|).
================================================================================
"""

from typing import Tuple, Dict, Any, Optional
import numpy as np
from src.icosahedral_qc.projectors import P_PAR
from src.icosahedral_qc.structure_factor import K_PAR, I1, I2, I3


# Projected hypercubic step vectors d_alpha in physical space: d_alpha = P_par e_alpha
D_ALPHA_PAR: np.ndarray = P_PAR
FACTOR_K: np.ndarray = 1.0 - np.exp(1j * (K_PAR @ D_ALPHA_PAR))


def evaluate_patch_observables(nodes: np.ndarray, X: np.ndarray, shift_vec: Optional[np.ndarray] = None) -> Dict[str, Any]:
    """
    Computes both:
      1. Bispectrum pseudoscalar chi_b
      2. Dynamical Graph-Laplacian circular dichroism D_lap
    on a finite cut-and-project patch X = nodes @ P_PAR.T.
    
    Args:
        nodes: (N, 6) int64 hypercubic lattice vectors
        X: (N, 3) float64 physical space coordinates
        shift_vec: Optional translation vector for translation invariance check
        
    Returns:
        Dict containing:
          'chi': float
          'D_lap': float
          'ratio': float
          'B': array of bispectrum values
          'delta_J_LR': array of circular dichroism values.
    """
    if shift_vec is not None:
        X = X + shift_vec[None, :]
    N = len(X)
    weights = np.array([64 ** i for i in range(6)], dtype=np.int64)
    offset = 32
    keys = (nodes + offset) @ weights
    sort_idx = np.argsort(keys)
    sorted_keys = keys[sort_idx]

    # Indicator functions for 6 directional forward bonds
    W_ind = np.zeros((N, 7), dtype=float)
    W_ind[:, 0] = 1.0
    for ax in range(6):
        nb = nodes.copy()
        nb[:, ax] += 1
        nb_keys = (nb + offset) @ weights
        pos = np.searchsorted(sorted_keys, nb_keys)
        valid = pos < N
        pos_v = pos[valid]
        match = sorted_keys[pos_v] == nb_keys[valid]
        src = np.where(valid)[0][match]
        W_ind[src, ax + 1] = 1.0

    F_all = np.zeros((len(K_PAR), 7), dtype=complex)
    chunk_size = 20000
    for start in range(0, N, chunk_size):
        end = min(N, start + chunk_size)
        Phi_chunk = np.exp(1j * (K_PAR @ X[start:end].T))
        F_all += Phi_chunk @ W_ind[start:end, :]
    if N > 0:
        F_all /= N

    F = F_all[:, 0]
    F_alpha_conj = np.conj(F_all[:, 1:].T)

    prod_F = F[I1] * F[I2] * F[I3]
    B = np.imag(prod_F)
    denom_chi = np.sum(np.abs(prod_F))
    chi = float(np.sum(np.abs(B)) / denom_chi) if denom_chi > 1e-15 else 0.0

    A_12 = F[I1] * F[I2]
    M_12_L = np.sum(FACTOR_K[I1, :] * FACTOR_K[I2, :] * F_alpha_conj[:, I3].T, axis=1)
    J_R = np.abs(A_12 + 1j * M_12_L) ** 2
    J_L = np.abs(A_12 - 1j * M_12_L) ** 2
    delta_J_LR = J_L - J_R
    denom_dlap = 4.0 * np.sum(np.abs(A_12) * np.abs(M_12_L))
    D_lap = float(np.sum(np.abs(delta_J_LR)) / denom_dlap) if denom_dlap > 1e-15 else 0.0

    ratio = float(D_lap / chi) if chi > 1e-12 else 0.0

    return {
        "chi": chi,
        "D_lap": D_lap,
        "ratio": ratio,
        "B": B,
        "delta_J_LR": delta_J_LR,
        "N": N
    }


def compute_laplacian_dichroism(nodes: np.ndarray, x_par: np.ndarray) -> float:
    """
    Computes D_lap for the given finite patch.
    """
    res = evaluate_patch_observables(nodes, x_par)
    return res["D_lap"]
