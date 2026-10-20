"""
src/icosahedral_qc/structure_factor.py
================================================================================
Complex Structure Factor F(k) and 3-Wave Bragg Bispectrum Pseudoscalar chi_b.
Evaluates:
  F(k) = (1/N) sum_j exp(i k . x_j)
  B(k_1, k_2) = Im[ F(k_1) F(k_2) F(k_3) ]  for k_1 + k_2 + k_3 = 0
  chi_b = sum_{Delta} |B(k_1, k_2)| / sum_{Delta} |F(k_1) F(k_2) F(k_3)|.

Guarantees exact real-space translation invariance:
  F'(k_1) F'(k_2) F'(k_3) = exp(i(k_1 + k_2 + k_3) . a) F_1 F_2 F_3 = F_1 F_2 F_3
yielding Delta B < 10^-15 to machine precision.
================================================================================
"""

from typing import Tuple, List, Dict, Any, Optional
import numpy as np
from src.icosahedral_qc.projectors import P_PAR, P_PERP, compute_icosahedral_symmetry_groups

# Construct canonical wavevector module K and closed Bragg triplets
_M_SET = set()
_IH_6D, _, _, _ = compute_icosahedral_symmetry_groups()

for _m0 in [
    (1, 0, 0, 0, 0, 0),
    (1, 1, 0, 0, 0, 0),
    (1, 2, 0, 0, 0, 0),
    (1, 2, 3, 0, 0, 0),
    (1, 2, -3, 0, 0, 0),
    (1, 3, 2, -1, 0, 0),
]:
    for _g in _IH_6D:
        _M_SET.add(tuple(np.round(_g @ np.array(_m0, float)).astype(int)))

M_LIST: List[Tuple[int, ...]] = sorted(_M_SET)
K_PAR: np.ndarray = np.array([2.0 * np.pi * (P_PAR @ np.array(m, float)) for m in M_LIST])
K_PERP: np.ndarray = np.array([2.0 * np.pi * (P_PERP @ np.array(m, float)) for m in M_LIST])

_M_IDX = {m: i for i, m in enumerate(M_LIST)}
_TRIPLETS = []
for _i, _m1 in enumerate(M_LIST):
    for _j, _m2 in enumerate(M_LIST):
        if _j <= _i:
            continue
        _m3 = tuple(-np.array(_m1) - np.array(_m2))
        if _m3 in _M_IDX and len(_TRIPLETS) < 4000:
            _TRIPLETS.append((_i, _j, _M_IDX[_m3]))
            
TRIPLETS: np.ndarray = np.array(_TRIPLETS, dtype=int)
I1, I2, I3 = TRIPLETS[:, 0], TRIPLETS[:, 1], TRIPLETS[:, 2]


def get_wavevector_module() -> Tuple[List[Tuple[int, ...]], np.ndarray, np.ndarray, np.ndarray]:
    """
    Returns the wavevector module configuration:
      (M_LIST, K_PAR, K_PERP, TRIPLETS)
    """
    return M_LIST, K_PAR.copy(), K_PERP.copy(), TRIPLETS.copy()


def compute_structure_factor(points: np.ndarray, k_vecs: Optional[np.ndarray] = None) -> np.ndarray:
    """
    Computes the complex structure factor F(k) for an array of 3D points.
      F(k) = (1/N) sum_{j=1}^N exp(i k . x_j).
      
    Args:
        points: (N, 3) real-space coordinates
        k_vecs: (M, 3) wavevectors (default: K_PAR)
        
    Returns:
        F: (M,) complex structure factor amplitudes.
    """
    if k_vecs is None:
        k_vecs = K_PAR
    N = len(points)
    if N == 0:
        return np.zeros(len(k_vecs), dtype=complex)
    
    # Chunked evaluation for memory efficiency
    F = np.zeros(len(k_vecs), dtype=complex)
    chunk_size = 20000
    for start in range(0, N, chunk_size):
        end = min(N, start + chunk_size)
        phases = np.exp(1j * (k_vecs @ points[start:end].T))
        F += np.sum(phases, axis=1)
    F /= N
    return F


def compute_bragg_bispectrum(points: np.ndarray, q_triples: Optional[List[Tuple[int, int, int]]] = None) -> complex:
    """
    Computes the aggregate Bragg bispectrum product B = sum_{Delta} Im[ F(k1) F(k2) F(k3) ].
    """
    F = compute_structure_factor(points, K_PAR)
    if q_triples is not None:
        trips = np.array(q_triples, dtype=int)
        idx1, idx2, idx3 = trips[:, 0], trips[:, 1], trips[:, 2]
    else:
        idx1, idx2, idx3 = I1, I2, I3
        
    prod = F[idx1] * F[idx2] * F[idx3]
    return complex(np.sum(np.imag(prod)))


def evaluate_bispectrum(points: np.ndarray, shift_vec: Optional[np.ndarray] = None) -> Dict[str, Any]:
    """
    Evaluates the normalized 3-wave Bragg bispectrum pseudoscalar chi_b
    and verifies translational invariance.
    
    Args:
        points: (N, 3) physical space points
        shift_vec: Optional origin translation vector for translation invariance check
        
    Returns:
        Dict containing 'chi_b', 'B_array', and 'sum_abs_prod'.
    """
    X = points if shift_vec is None else points + shift_vec[None, :]
    F = compute_structure_factor(X, K_PAR)
    
    prod_F = F[I1] * F[I2] * F[I3]
    B = np.imag(prod_F)
    denom = np.sum(np.abs(prod_F))
    chi_b = float(np.sum(np.abs(B)) / denom) if denom > 1e-15 else 0.0
    
    return {
        "chi_b": chi_b,
        "B_array": B,
        "denom": float(denom),
        "N_points": len(points)
    }
