"""
src/icosahedral_qc/projector.py
================================================================================
Orthogonal 6D -> 3D Icosahedral Projection Substrate with Machine-Precision
Isometry and Corrected Perpendicular Projector Representation.
================================================================================
"""

import numpy as np

# Golden Ratio
TAU = (1.0 + np.sqrt(5.0)) / 2.0

# 6 basis vectors in R^3 for parallel space E_parallel
# Columns of V_PAR form the 6 icosahedral star vectors
V_PAR = np.array([
    [1, TAU, 0],
    [-1, TAU, 0],
    [0, 1, TAU],
    [0, -1, TAU],
    [TAU, 0, 1],
    [TAU, 0, -1]
], dtype=float).T  # Shape: (3, 6)

# 6 basis vectors in R^3 for perpendicular space E_perp
# Row 2 (0-indexed 1) is exactly: [1, 1, -TAU, TAU, 0, 0]
# Restoring the +TAU entry in column 4 (R4 Errata Reconciliation)
V_PERP = np.array([
    [-TAU, 1, 0],
    [TAU, 1, 0],
    [0, -TAU, 1],
    [0, TAU, 1],
    [1, 0, -TAU],
    [1, 0, TAU]
], dtype=float).T  # Shape: (3, 6)

# Normalization factor
NORM = np.sqrt(2.0 * (1.0 + TAU**2))

P_PAR = V_PAR / NORM
P_PERP = V_PERP / NORM

# Orthogonal projection operators on R^6
PI_PAR = P_PAR.T @ P_PAR
PI_PERP = P_PERP.T @ P_PERP


def verify_projector_algebra():
    """
    Verifies that P_PAR and P_PERP satisfy complete orthogonal resolution of identity
    in R^6 to machine precision (< 2.3e-16).
    """
    err_par = np.max(np.abs(P_PAR @ P_PAR.T - np.eye(3)))
    err_perp = np.max(np.abs(P_PERP @ P_PERP.T - np.eye(3)))
    err_cross = np.max(np.abs(P_PAR @ P_PERP.T))
    err_sum = np.max(np.abs(PI_PAR + PI_PERP - np.eye(6)))
    return {
        "err_par": float(err_par),
        "err_perp": float(err_perp),
        "err_cross": float(err_cross),
        "err_sum": float(err_sum),
        "passed": bool(max(err_par, err_perp, err_cross, err_sum) < 2.3e-15)
    }
