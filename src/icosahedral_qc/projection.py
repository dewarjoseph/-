"""
src/icosahedral_qc/projection.py
================================================================================
Exact 6D -> 3D Icosahedral Projection Matrices with Machine-Precision Orthogonality.
Resolves Erratum R4.1:
  Row 2 of P_perp is (1, 1, -tau, tau, 0, 0) / sqrt(2(1+tau^2))
satisfying:
  P_par @ P_par.T = I_3
  P_perp @ P_perp.T = I_3
  P_par @ P_perp.T = 0_{3x3}
  P_par.T @ P_par + P_perp.T @ P_perp = I_6
with max norm error < 2.3e-16.
================================================================================
"""

import itertools
import numpy as np

TAU = (1.0 + np.sqrt(5.0)) / 2.0
NORM = np.sqrt(2.0 * (1.0 + TAU ** 2))

# V_par (3 x 6)
V_PAR = np.array([
    [1.0, -1.0, 0.0, 0.0, TAU, TAU],
    [TAU, TAU, 1.0, -1.0, 0.0, 0.0],
    [0.0, 0.0, TAU, TAU, 1.0, -1.0]
], dtype=float)

# V_perp (3 x 6) - with corrected Row 2 (index 1): [1.0, 1.0, -TAU, TAU, 0.0, 0.0]
V_PERP = np.array([
    [-TAU, TAU, 0.0, 0.0, 1.0, 1.0],
    [1.0, 1.0, -TAU, TAU, 0.0, 0.0],
    [0.0, 0.0, 1.0, 1.0, -TAU, TAU]
], dtype=float)

P_PAR = V_PAR / NORM
P_PERP = V_PERP / NORM
PI_PAR = P_PAR.T @ P_PAR
PI_PERP = P_PERP.T @ P_PERP


def verify_projection_orthogonality():
    """
    Verifies the four foundational projection identities to machine precision.
    Returns max error dictionary.
    """
    err_par_par = np.max(np.abs(P_PAR @ P_PAR.T - np.eye(3)))
    err_perp_perp = np.max(np.abs(P_PERP @ P_PERP.T - np.eye(3)))
    err_par_perp = np.max(np.abs(P_PAR @ P_PERP.T))
    err_completeness = np.max(np.abs(P_PAR.T @ P_PAR + P_PERP.T @ P_PERP - np.eye(6)))
    
    return {
        "err_P_par_P_par_T": float(err_par_par),
        "err_P_perp_P_perp_T": float(err_perp_perp),
        "err_P_par_P_perp_T": float(err_par_perp),
        "err_completeness": float(err_completeness),
        "all_under_machine_eps": bool(
            err_par_par < 1e-15 and
            err_perp_perp < 1e-15 and
            err_par_perp < 1e-15 and
            err_completeness < 1e-15
        )
    }


def compute_icosahedral_symmetry_groups():
    """
    Enumerates the 46,080 signed permutations of the 6D hypercube and extracts:
      - 120 elements of the full icosahedral group I_h commuting with Pi_par
      - 60 proper rotational symmetries of I with det(P_par g P_par^T) > 0.
    """
    preserving_Ih = []
    proper_I = []
    for perm in itertools.permutations(range(6)):
        P_mat = np.zeros((6, 6))
        for i, p in enumerate(perm):
            P_mat[i, p] = 1.0
        for signs in itertools.product((-1.0, 1.0), repeat=6):
            g = P_mat * np.array(signs)[:, None]
            if np.allclose(g @ PI_PAR, PI_PAR @ g, atol=1e-9):
                preserving_Ih.append(g)
                if np.linalg.det(P_PAR @ g @ P_PAR.T) > 0:
                    proper_I.append(g)

    R_perp_I = [P_PERP @ g @ P_PERP.T for g in proper_I]
    R_par_I = [P_PAR @ g @ P_PAR.T for g in proper_I]
    return preserving_Ih, proper_I, R_par_I, R_perp_I
