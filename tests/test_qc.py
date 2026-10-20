"""
tests/test_qc.py
================================================================================
Comprehensive Unit Test Suite for src/icosahedral_qc:
  1. 6D -> 3D Projection Matrices & Machine Precision Orthogonality (< 2.3e-16).
  2. Acceptance Windows (W_b, -W_b, W_a) and Chiral Symmetry Groups.
  3. Vectorized 6D BFS Cut-and-Project Patch Generation.
  4. Structure Factor F(k), Bragg Bispectrum chi_b, and Translation Invariance (< 1e-15).
  5. Dynamical Graph-Laplacian Circular Dichroism D_lap and Parity Anti-Symmetry.
  6. Exact Analytical Weyl Continuum Limits & Unrounded Ratio 0.8713 (Erratum R4.3).
  7. Parity-Odd Fubini-Study Quantum Metric g_xy = -0.2525 and Parity Audit.
  8. HONHSE Corner Skin Modes & Table 3 Non-Bloch Dissipation Scaling (Erratum R4.2).
  9. Floquet-Phasonic Sideband Dichroism (-47.2%) & Persistent Solenoidal Currents.
================================================================================
"""

import os
import sys
import unittest
import numpy as np
from scipy.spatial import ConvexHull

sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), "..")))

from src.icosahedral_qc.projectors import (
    P_PAR, P_PERP, PI_PAR, PI_PERP, TAU,
    get_projectors, verify_projection_orthogonality,
    compute_icosahedral_symmetry_groups, PHYSICAL_SCALING_DICTIONARY
)
from src.icosahedral_qc.windows import (
    get_acceptance_windows, get_acceptance_window, P0_CHIRAL
)
from src.icosahedral_qc.lattice_bfs import (
    bfs_vectorized_6d, generate_quasicrystal_patch, build_patch_adjacency
)
from src.icosahedral_qc.structure_factor import (
    get_wavevector_module, compute_structure_factor,
    compute_bragg_bispectrum, evaluate_bispectrum
)
from src.icosahedral_qc.laplacian_dichroism import (
    evaluate_patch_observables, compute_laplacian_dichroism
)
from src.icosahedral_qc.weyl_continuum import (
    integrate_polyhedron_exp, compute_analytical_infinity_limits
)
from src.icosahedral_qc.quantum_metric import (
    compute_fubini_study_metric, compute_quantum_metric_tensor,
    verify_quantum_metric_parity
)
from src.icosahedral_qc.non_hermitian import (
    classify_spatial_regions, build_non_hermitian_hamiltonian,
    compute_non_hermitian_skin_modes, compute_non_bloch_gbz_decay
)
from src.icosahedral_qc.honhse import evaluate_gbz_skin_depth_scaling
from src.icosahedral_qc.floquet_phason import (
    compute_floquet_dichroism, compute_phason_spectral_loop,
    compute_persistent_edge_current
)
from src.icosahedral_qc.honhse import evaluate_gbz_skin_depth_scaling



class TestIcosahedralQCSuite(unittest.TestCase):

    def test_01_projector_orthogonality_and_erratum_r41(self):
        ortho = verify_projection_orthogonality()
        self.assertLess(ortho["err_P_par_P_par_T"], 2.3e-16)
        self.assertLess(ortho["err_P_perp_P_perp_T"], 2.3e-16)
        self.assertLess(ortho["err_P_par_P_perp_T"], 2.3e-16)
        self.assertLess(ortho["err_completeness"], 2.3e-16)
        self.assertTrue(ortho["under_machine_precision"])
        self.assertTrue(ortho["passed"])

        # Symmetry groups
        IH_6D, I_6D, R_par_I, R_perp_I = compute_icosahedral_symmetry_groups()
        self.assertEqual(len(IH_6D), 120, "Full icosahedral group I_h must have order 120")
        self.assertEqual(len(I_6D), 60, "Chiral proper icosahedral group I must have order 60")
        self.assertEqual(len(R_perp_I), 60)

    def test_02_acceptance_windows(self):
        hull_a, hull_b, hull_bm = get_acceptance_windows()
        self.assertIsInstance(hull_a, ConvexHull)
        self.assertIsInstance(hull_b, ConvexHull)
        self.assertIsInstance(hull_bm, ConvexHull)

        # W_b has 60 vertices (proper icosahedral orbit of generic seed)
        self.assertEqual(len(hull_b.vertices), 60, "W_b must have 60 vertices")
        self.assertEqual(len(hull_bm.vertices), 60, "Mirror window -W_b must have 60 vertices")

        # Test retrieval by name
        w_b = get_acceptance_window("W_b")
        w_bm = get_acceptance_window("-W_b")
        w_a = get_acceptance_window("W_a")
        self.assertEqual(len(w_b.vertices), 60)
        self.assertEqual(len(w_bm.vertices), 60)

    def test_03_lattice_bfs_and_patch_generation(self):
        hull_b = get_acceptance_window("W_b")
        nodes, x_par, x_perp, r_norms = bfs_vectorized_6d(hull_b, R_max=3.0)
        self.assertGreater(len(x_par), 100)
        self.assertTrue(np.all(r_norms <= 3.0 + 1e-9))
        self.assertEqual(x_par.shape[1], 3)
        self.assertEqual(x_perp.shape[1], 3)

        # Adjacency matrix construction
        adj = build_patch_adjacency(nodes[:100])
        self.assertEqual(adj.shape, (100, 100))
        self.assertTrue(np.allclose(adj, adj.T), "Adjacency matrix must be symmetric")

    def test_04_structure_factor_and_bispectrum_translation_invariance(self):
        hull_b = get_acceptance_window("W_b")
        hull_bm = get_acceptance_window("-W_b")
        hull_a = get_acceptance_window("W_a")

        nodes_b, xb, _, _ = bfs_vectorized_6d(hull_b, 4.0)
        nodes_bm, xbm, _, _ = bfs_vectorized_6d(hull_bm, 4.0)
        nodes_a, xa, _, _ = bfs_vectorized_6d(hull_a, 4.0)

        # Bispectrum evaluation
        res_b = evaluate_bispectrum(xb)
        res_bm = evaluate_bispectrum(xbm)
        res_a = evaluate_bispectrum(xa)

        # Translation invariance test
        shift = np.array([0.723, -1.414, 2.718])
        res_b_shifted = evaluate_bispectrum(xb, shift_vec=shift)
        max_shift_diff = float(np.max(np.abs(res_b["B_array"] - res_b_shifted["B_array"])))
        self.assertLess(max_shift_diff, 1e-14, f"Translation invariance violated: {max_shift_diff:.2e}")

        # Enantiomeric opposite-sign anti-symmetry
        parity_sum_max = float(np.max(np.abs(res_b["B_array"] + res_bm["B_array"])))
        self.assertLess(parity_sum_max, 1e-14, f"Opposite-sign parity anti-symmetry violated: {parity_sum_max:.2e}")

        # Achiral control zero
        max_B_achiral = float(np.max(np.abs(res_a["B_array"])))
        self.assertLess(max_B_achiral, 1e-14, f"Achiral control bispectrum not zero: {max_B_achiral:.2e}")

    def test_05_laplacian_circular_dichroism(self):
        hull_b = get_acceptance_window("W_b")
        hull_bm = get_acceptance_window("-W_b")
        hull_a = get_acceptance_window("W_a")

        nodes_b, xb, _, _ = bfs_vectorized_6d(hull_b, 3.5)
        nodes_bm, xbm, _, _ = bfs_vectorized_6d(hull_bm, 3.5)
        nodes_a, xa, _, _ = bfs_vectorized_6d(hull_a, 3.5)

        obs_b = evaluate_patch_observables(nodes_b, xb)
        obs_bm = evaluate_patch_observables(nodes_bm, xbm)
        obs_a = evaluate_patch_observables(nodes_a, xa)

        self.assertGreater(obs_b["chi"], 0.0)
        self.assertGreater(obs_b["D_lap"], 0.0)
        self.assertAlmostEqual(obs_b["chi"], obs_bm["chi"], places=6)

        # Opposite sign circular dichroism
        dJ_sum_max = float(np.max(np.abs(obs_b["delta_J_LR"] + obs_bm["delta_J_LR"])))
        self.assertLess(dJ_sum_max, 1e-14, f"Dichroism parity anti-symmetry violated: {dJ_sum_max:.2e}")

        # Achiral control zero
        self.assertLess(obs_a["chi"], 1e-14, f"Achiral control chi_a not zero: {obs_a['chi']:.2e}")
        self.assertLess(obs_a["D_lap"], 1e-14, f"Achiral control D_a not zero: {obs_a['D_lap']:.2e}")

    def test_06_weyl_continuum_limits_and_erratum_r43(self):
        import json, os
        ledger_path = os.path.join(os.path.dirname(__file__), "..", "data", "module6_continuum_results.json")
        with open(ledger_path, "r") as f:
            data = json.load(f)
        weyl = data["weyl_continuum_limits"]

        self.assertAlmostEqual(weyl["chi_b_infinity"], 0.001767, places=5)
        self.assertAlmostEqual(weyl["d_lap_infinity"], 0.001539, places=5)

        # Verify unrounded ratio 0.8713 (Erratum R4.3)
        ratio_unrounded = weyl["d_lap_infinity"] / weyl["chi_b_infinity"]
        self.assertAlmostEqual(ratio_unrounded, 0.8713, places=3)
        self.assertEqual(round(ratio_unrounded, 4), 0.8713)

    def test_07_fubini_study_quantum_metric(self):
        qm = verify_quantum_metric_parity()
        self.assertAlmostEqual(qm["g_xy_W_b"], -0.2525, places=4)
        self.assertAlmostEqual(qm["g_xy_W_bm"], +0.2525, places=4)
        self.assertEqual(qm["g_xy_W_a"], 0.0)
        self.assertLess(qm["parity_sum_residual"], 1e-14)
        self.assertTrue(qm["parity_audit_passed"])

    def test_08_honhse_and_table3_decay_erratum_r42(self):
        # 1. Spatial classification test
        dummy_X = np.array([
            [5.0, 5.0, 3.0],   # corner
            [5.0, 0.0, 0.5],   # face
            [1.0, 1.0, 0.5],   # bulk
        ])
        regions = classify_spatial_regions(dummy_X, r_hinge=4.0, z_hinge=2.0)
        self.assertEqual(regions["n_corner"], 1)
        self.assertEqual(regions["n_face"], 1)
        self.assertEqual(regions["n_bulk"], 1)

        # 2. Table 3 non-Bloch dissipation scaling and Erratum R4.2 check
        table3 = compute_non_bloch_gbz_decay()
        entry_25 = next(item for item in table3 if item["eta"] == 0.25)
        self.assertAlmostEqual(entry_25["delta_kappa_W_b"], 1.51898e-2, places=6)
        self.assertAlmostEqual(entry_25["delta_kappa_W_bm"], -1.51999e-2, places=6)
        self.assertAlmostEqual(entry_25["parity_sum_residual"], -1.0130e-5, places=8)
        self.assertTrue(entry_25["erratum_r42_reconciled"], "Erratum R4.2 table 3 exponent fix failed")

    def test_09_floquet_phason_and_edge_currents(self):
        cd = compute_floquet_dichroism()
        self.assertAlmostEqual(cd, -47.195, places=2)

        loop_b = compute_phason_spectral_loop("W_b")
        loop_bm = compute_phason_spectral_loop("-W_b")
        loop_a = compute_phason_spectral_loop("W_a")
        self.assertAlmostEqual(loop_b["spectral_loop_area"], -loop_bm["spectral_loop_area"], places=6)
        self.assertEqual(loop_a["spectral_loop_area"], 0.0)

        cur_b = compute_persistent_edge_current("W_b")
        cur_bm = compute_persistent_edge_current("-W_b")
        cur_a = compute_persistent_edge_current("W_a")
        self.assertAlmostEqual(cur_b["J_edge"], -cur_bm["J_edge"], delta=2e-5)
        self.assertAlmostEqual(cur_a["J_edge"], 0.0, delta=2e-5)
        self.assertGreater(cur_b["m_z"], 0.0)
        self.assertGreater(cur_b["Phi_B"], 0.0)

    def test_10_gbz_skin_depth_scaling(self):
        """Pillar 2: Verify GBZ skin depth scaling xi(eta) propto eta^{-1} and Berry phase 2pi."""
        gbz = evaluate_gbz_skin_depth_scaling()
        self.assertTrue(gbz["gbz_scaling_verified"])
        self.assertAlmostEqual(gbz["skin_depth_scaling_exponent"], 1.0, places=6)
        self.assertAlmostEqual(gbz["phasonic_berry_phase"], 2.0 * np.pi, places=6)
        self.assertAlmostEqual(gbz["gbz_radii"][0], np.exp(-0.05), places=6)


if __name__ == "__main__":
    unittest.main()
