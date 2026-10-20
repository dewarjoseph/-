"""
tests/test_errata.py
================================================================================
Comprehensive Unit Test Suite for Pre-Publication Mathematical Errata Reconciliation (R4):
  1. Erratum R4.1: Restoration of +tau in P_perp Row 2 Col 4;
     Verification of all 4 projector identities to machine precision (< 2.3e-16).
  2. Erratum R4.2: Section 4.3 Table 3 at eta=0.25 exponent typo fix (10^-3 -> 10^-5);
     Verification of parity sum residual = -1.0130e-5.
  3. Erratum R4.3: Section 2.3 Eq. (10) Gauss-Legendre quadrature ratio resolution:
     Unrounded ratio 0.87127... -> 0.8713 vs rounded 0.001539 / 0.001767 -> 0.8710.
  4. Erratum R4.4: Multi-domain continuum operator scaling and physical unit dictionary.
================================================================================
"""

import os
import sys
import unittest
import numpy as np

sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), "..")))

from src.icosahedral_qc.projectors import (
    P_PAR, P_PERP, V_PAR, V_PERP, TAU, NORM,
    verify_projection_orthogonality, PHYSICAL_SCALING_DICTIONARY
)
from src.icosahedral_qc.windows import get_acceptance_window
from src.icosahedral_qc.weyl_continuum import compute_analytical_infinity_limits
from src.icosahedral_qc.non_hermitian import compute_non_bloch_gbz_decay


class TestErrataReconciliationSuite(unittest.TestCase):

    def test_01_erratum_r41_projector_row2_tau_restoration(self):
        """
        Erratum R4.1:
        In draft Section 2.1 Eq. (1), Row 2 of P_perp omitted the 4th column entry +tau.
        Verify that:
          1. The erroneous matrix with 0 in Row 2 Col 4 fails projector algebra.
          2. The restored matrix with +tau in Row 2 Col 4 satisfies all 4 identities < 2.3e-16.
        """
        # Erroneous draft matrix
        V_perp_erroneous = np.array([
            [-TAU, TAU, 0.0, 0.0, 1.0, 1.0],
            [1.0, 1.0, -TAU, 0.0, 0.0, 0.0],  # missing +TAU
            [0.0, 0.0, 1.0, 1.0, -TAU, TAU]
        ], dtype=float)
        P_perp_erroneous = V_perp_erroneous / NORM

        # Show that the erroneous matrix FAILS orthogonality
        err_erroneous_perp = np.max(np.abs(P_perp_erroneous @ P_perp_erroneous.T - np.eye(3)))
        err_erroneous_cross = np.max(np.abs(P_PAR @ P_perp_erroneous.T))
        self.assertGreater(err_erroneous_perp, 0.1, "Erroneous matrix should fail P_perp P_perp^T = I_3")
        self.assertGreater(err_erroneous_cross, 0.1, "Erroneous matrix should fail P_par P_perp^T = 0")

        # Corrected matrix
        ortho = verify_projection_orthogonality()
        self.assertLess(ortho["err_P_par_P_par_T"], 2.3e-16, "P_par P_par^T >= 2.3e-16")
        self.assertLess(ortho["err_P_perp_P_perp_T"], 2.3e-16, "P_perp P_perp^T >= 2.3e-16")
        self.assertLess(ortho["err_P_par_P_perp_T"], 2.3e-16, "P_par P_perp^T >= 2.3e-16")
        self.assertLess(ortho["err_completeness"], 2.3e-16, "Completeness >= 2.3e-16")
        self.assertTrue(ortho["under_machine_precision"])
        self.assertTrue(ortho["passed"])

        # Also assert against strict 1e-15 acceptance threshold
        self.assertLess(ortho["max_error"], 1e-15)

    def test_02_erratum_r42_table3_exponent_typo_reconciliation(self):
        """
        Erratum R4.2:
        In Section 4.3 Table 3, the residual at eta=0.25 was misprinted as -1.0130e-3.
        The true value is:
          Delta_kappa(W_b)  = +1.51898e-2
          Delta_kappa(-W_b) = -1.51999e-2
          Sum Residual      = -1.0130e-5  (fixing the 10^-3 exponent typo).
        """
        table3 = compute_non_bloch_gbz_decay()
        entry_25 = next(item for item in table3 if item["eta"] == 0.25)

        dk_b = entry_25["delta_kappa_W_b"]
        dk_bm = entry_25["delta_kappa_W_bm"]
        res = entry_25["parity_sum_residual"]

        self.assertAlmostEqual(dk_b, +1.51898e-2, places=6)
        self.assertAlmostEqual(dk_bm, -1.51999e-2, places=6)
        
        # Exact residual test
        exact_expected_residual = -1.0130e-5
        self.assertAlmostEqual(res, exact_expected_residual, places=8)
        self.assertTrue(entry_25["erratum_r42_reconciled"])

        # Prove that relative error with 10^-5 is ~0.066%, whereas 10^-3 would be ~6.66%
        rel_error_10_minus_5 = abs(res) / abs(dk_b)
        self.assertLess(rel_error_10_minus_5, 0.001, "Relative residual must be < 0.1% (sub-percent boundary effect)")

        rel_error_10_minus_3 = 1.0130e-3 / abs(dk_b)
        self.assertGreater(rel_error_10_minus_3, 0.05, "Typo 10^-3 would erroneously imply >5% parity violation")

    def test_03_erratum_r43_unrounded_quadrature_ratio(self):
        """
        Erratum R4.3:
        Section 2.3 Eq. (10) reports D_lap(infinity)/chi_b(infinity) = 0.8713.
        Verify that this is obtained from the unrounded 16-point Gauss-Legendre quadrature:
          chi_b(infinity)   = 0.00176684...
          D_lap(infinity)   = 0.00153940...
          ratio_unrounded   = 0.8712716... -> rounds to 0.8713.
        Naive division of 6-digit rounded figures gives:
          0.001539 / 0.001767 = 0.870967... -> rounds to 0.8710 != 0.8713.
        """
        hull_b = get_acceptance_window("W_b")
        weyl = compute_analytical_infinity_limits(hull_b, n_gl=16)

        chi_inf = weyl["chi_b_infinity"]
        dlap_inf = weyl["d_lap_infinity"]
        ratio_unrounded = weyl["ratio_unrounded"]
        ratio_rounded = weyl["ratio_rounded_4decimals"]

        # Confirm unrounded ratio rounds to 0.8713
        self.assertEqual(ratio_rounded, 0.8713)
        self.assertAlmostEqual(ratio_unrounded, 0.8712716, places=5)

        # Demonstrate the truncation difference of rounded values
        rounded_chi = 0.001767
        rounded_dlap = 0.001539
        naive_ratio = rounded_dlap / rounded_chi
        naive_ratio_rounded = round(naive_ratio, 4)
        
        self.assertEqual(naive_ratio_rounded, 0.8710)
        self.assertNotEqual(naive_ratio_rounded, ratio_rounded, "Unrounded ratio 0.8713 differs from truncated 0.8710")

    def test_04_erratum_r44_physical_scaling_dictionary(self):
        """
        Erratum R4.4:
        Verify the physical scaling dictionary across Photonic, Biomolecular, and Cosmological regimes.
        """
        psd = PHYSICAL_SCALING_DICTIONARY
        self.assertIn("photonic_metamaterials", psd)
        self.assertIn("biomolecular_capsids", psd)
        self.assertIn("flrw_cosmology", psd)
        self.assertIn("continuum_operator_mapping", psd)

        # Photonic Metamaterials checks
        photo = psd["photonic_metamaterials"]
        self.assertIn("um", photo["length_scale_a0"])
        self.assertIn("THz", photo["frequency_scale_omega0"])
        self.assertIn("C_opt", photo["optical_chirality_density"])

        # Biomolecular Capsids checks
        bio = psd["biomolecular_capsids"]
        self.assertIn("nm", bio["length_scale_a0"])
        self.assertIn("k_B T", bio["corner_torque_tau_z"])
        self.assertIn("Tirion", bio["elastic_network_operator"])

        # FLRW Cosmology checks
        cosmo = psd["flrw_cosmology"]
        self.assertIn("H_0^-1", cosmo["length_scale_a0"])
        self.assertIn("Delta_alpha", cosmo["chiral_metric_g_xy"])
        self.assertIn("B_seed", cosmo["magnetic_seed_flux"])

        # Continuum mapping
        mapping = psd["continuum_operator_mapping"]
        self.assertIn("nabla^2", mapping["laplacian_wave_operator"])
        self.assertTrue("momentum_minimal_coupling" in mapping or "minimal_coupling" in mapping)


if __name__ == "__main__":
    unittest.main()
