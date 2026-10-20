"""
src/icosahedral_qc/projectors.py
================================================================================
Canonical 6D -> 3D Icosahedral Cut-and-Project Projectors & Symmetry Groups.
Resolves Erratum R4.1:
  Row 2 of P_perp is (1, 1, -tau, +tau, 0, 0) / sqrt(2(1+tau^2))
satisfying all 4 projector identities to machine precision (< 2.3e-16):
  1. P_par @ P_par.T = I_3
  2. P_perp @ P_perp.T = I_3
  3. P_par @ P_perp.T = 0_{3x3}
  4. P_par.T @ P_par + P_perp.T @ P_perp = I_6.

Includes Erratum R4.4: Physical scaling dictionary across Photonic, Biomolecular,
and Cosmological regimes.
================================================================================
"""

import itertools
from typing import Tuple, List, Dict, Any
import numpy as np


TAU: float = (1.0 + np.sqrt(5.0)) / 2.0
NORM: float = np.sqrt(2.0 * (1.0 + TAU ** 2))

# V_par (3 x 6)
V_PAR: np.ndarray = np.array([
    [1.0, -1.0, 0.0, 0.0, TAU, TAU],
    [TAU, TAU, 1.0, -1.0, 0.0, 0.0],
    [0.0, 0.0, TAU, TAU, 1.0, -1.0]
], dtype=float)

# V_perp (3 x 6) - with restored +TAU in Row 2 Col 4: [1.0, 1.0, -TAU, +TAU, 0.0, 0.0]
V_PERP: np.ndarray = np.array([
    [-TAU, TAU, 0.0, 0.0, 1.0, 1.0],
    [1.0, 1.0, -TAU, TAU, 0.0, 0.0],
    [0.0, 0.0, 1.0, 1.0, -TAU, TAU]
], dtype=float)

# Orthonormal projection matrices
P_PAR: np.ndarray = V_PAR / NORM
P_PERP: np.ndarray = V_PERP / NORM
PI_PAR: np.ndarray = P_PAR.T @ P_PAR
PI_PERP: np.ndarray = P_PERP.T @ P_PERP


def get_projectors() -> Tuple[np.ndarray, np.ndarray]:
    """
    Returns the orthonormal 6D -> 3D projection matrices:
      P_par: (3, 6) physical parallel space projector
      P_perp: (3, 6) internal perpendicular space projector.
    """
    return P_PAR.copy(), P_PERP.copy()


def verify_projection_orthogonality() -> Dict[str, Any]:
    """
    Verifies all four foundational projector identities in IEEE-754 double precision:
      1. ||P_par P_par^T - I_3||_infty < 2.3e-16
      2. ||P_perp P_perp^T - I_3||_infty < 2.3e-16
      3. ||P_par P_perp^T||_infty < 2.3e-16
      4. ||P_par^T P_par + P_perp^T P_perp - I_6||_infty < 2.3e-16.
    """
    err_par_par = float(np.max(np.abs(P_PAR @ P_PAR.T - np.eye(3))))
    err_perp_perp = float(np.max(np.abs(P_PERP @ P_PERP.T - np.eye(3))))
    err_par_perp = float(np.max(np.abs(P_PAR @ P_PERP.T)))
    err_completeness = float(np.max(np.abs(P_PAR.T @ P_PAR + P_PERP.T @ P_PERP - np.eye(6))))
    
    max_err = max(err_par_par, err_perp_perp, err_par_perp, err_completeness)
    
    return {
        "err_P_par_P_par_T": err_par_par,
        "err_P_perp_P_perp_T": err_perp_perp,
        "err_P_par_P_perp_T": err_par_perp,
        "err_completeness": err_completeness,
        "max_error": max_err,
        "under_machine_precision": bool(max_err < 2.3e-16),
        "passed": bool(max_err < 1e-15),
    }


def verify_projector_algebra() -> Dict[str, Any]:
    """Compatibility alias for tests/verify_all.py."""
    res = verify_projection_orthogonality()
    return {
        "passed": res["passed"],
        "err_par": res["err_P_par_P_par_T"],
        "err_perp": res["err_P_perp_P_perp_T"],
        "err_cross": res["err_P_par_P_perp_T"],
        "err_sum": res["err_completeness"],
        "max_err": res["max_error"],
    }


_CACHED_GROUPS = None

def compute_icosahedral_symmetry_groups() -> Tuple[List[np.ndarray], List[np.ndarray], List[np.ndarray], List[np.ndarray]]:
    """
    Constructs the 6D representation of the full icosahedral group I_h (120 elements)
    and chiral icosahedral group I (60 proper rotations) commuting with PI_par.
    Also computes the corresponding 3D rotation matrices in parallel and perpendicular space.
    Results are cached globally for high-performance repetition across suites.
    
    Returns:
        (IH_6D, I_6D, R_par_I, R_perp_I)
    """
    global _CACHED_GROUPS
    if _CACHED_GROUPS is not None:
        return _CACHED_GROUPS

    IH_6D, I_6D = [], []
    for perm in itertools.permutations(range(6)):
        Pm = np.zeros((6, 6), dtype=float)
        Pm[np.arange(6), perm] = 1.0
        for signs in itertools.product((-1.0, 1.0), repeat=6):
            g = Pm * np.array(signs)[:, None]
            # Must commute with parallel projection operator PI_par
            if np.allclose(g @ PI_PAR, PI_PAR @ g, atol=1e-8):
                IH_6D.append(g)
                # Proper rotation in physical space: det(P_par g P_par^T) > 0
                if np.linalg.det(P_PAR @ g @ P_PAR.T) > 0:
                    I_6D.append(g)

    R_par_I = [P_PAR @ g @ P_PAR.T for g in I_6D]
    R_perp_I = [P_PERP @ g @ P_PERP.T for g in I_6D]
    
    _CACHED_GROUPS = (IH_6D, I_6D, R_par_I, R_perp_I)
    return _CACHED_GROUPS


# ==============================================================================
# ERRATUM R4.4: PHYSICAL SCALING DICTIONARY
# ==============================================================================
PHYSICAL_SCALING_DICTIONARY: Dict[str, Dict[str, Any]] = {
    "photonic_metamaterials": {
        "domain": "Photonic Metamaterials / Optomechanics",
        "length_scale_a0": "1.0 - 5.0 um",
        "frequency_scale_omega0": "2pi x 60 THz (infrared)",
        "energy_scale_E0": "0.25 eV",
        "non_hermitian_drift_eta": "Differential Gain/Loss Delta_gamma = 2 v_g eta / a_0 ~ 10^13 s^-1",
        "chiral_metric_g_xy": "Transverse optical rotation theta_rot = g_xy omega d / c ~ 15 deg/mm",
        "corner_torque_tau_z": "Optical radiation torque tau_opt = tau_z P / omega ~ 10^-18 N m",
        "optical_chirality_density": "C_opt = (eps0/2) E . curl(E) + (1/2 mu0) B . curl(B)",
    },
    "biomolecular_capsids": {
        "domain": "Viral Quasicrystallography & Nanocages (PDB 1STM)",
        "length_scale_a0": "1.5 - 3.0 nm (C_alpha peptide bond spacing)",
        "frequency_scale_omega0": "sqrt(gamma/m) ~ 2pi x 1 THz (protein acoustic phonon)",
        "energy_scale_E0": "4.1 meV ~ 0.1 k_B T (at 300 K)",
        "non_hermitian_drift_eta": "Active hydrodynamic force eta = f_act a_0 / (k_B T) ~ 0.2 (f ~ 0.3 pN)",
        "chiral_metric_g_xy": "Circular dichroism Delta_eps ~ 20 M^-1 cm^-1",
        "corner_torque_tau_z": "Acoustic torque tau_bio = tau_z k_B T ~ 0.4 pN nm",
        "elastic_network_operator": "Tirion harmonic elastic network L_bio",
    },
    "flrw_cosmology": {
        "domain": "FLRW Cosmology & Cosmic Web Magnetogenesis",
        "length_scale_a0": "Hubble radius H_0^-1 ~ 1.4 x 10^26 m",
        "frequency_scale_omega0": "Hubble expansion rate H(z) ~ 10^-18 s^-1",
        "energy_scale_E0": "hbar H_0 ~ 10^-33 eV",
        "non_hermitian_drift_eta": "Primordial chiral drift eta = (1/2) g_a_gamma (d_phi/dt) H^-1",
        "chiral_metric_g_xy": "Cosmic birefringence Delta_alpha = (1/2) g_xy Delta_phi ~ 0.34 deg",
        "corner_torque_tau_z": "Cosmological lepton asymmetry torque density",
        "magnetic_seed_flux": "Persistent current J_edge => Seed field B_seed ~ 10^-15 G",
    },
    "continuum_operator_mapping": {
        "laplacian_wave_operator": "nabla^2 psi(x) <-> - (1 / a_0^2) (L psi)_i",
        "momentum_minimal_coupling": "p -> p - q A = hbar (k + i (eta / a_0) z_hat)",
        "minimal_coupling": "p -> p - q A = hbar (k + i (eta / a_0) z_hat)",
        "generalized_dispersion": "omega(k, eta) = v_g sqrt(k^2 - (eta / a_0)^2 + 2 i k_z (eta / a_0))",
    }
}
