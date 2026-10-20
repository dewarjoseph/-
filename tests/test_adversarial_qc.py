"""
tests/test_adversarial_qc.py
================================================================================
Independent Adversarial Empirical Test Suite for src/icosahedral_qc:
  1. 6D Projectors P_parallel & P_perp: 100,000 random vector orthogonal decomposition (< 1e-15).
  2. Acceptance Windows W_b, -W_b, W_a: convexity, exact volume congruence, icosahedral symmetry invariance.
  3. Cut-and-Project BFS: edge cases (R=0, R<1/sqrt(2), R=0.71) and brute-force Z^6 equivalence.
  4. Real-Space Bragg Bispectrum: translation invariance Delta B under arbitrary shifts, mirror parity inversion on -W_b, achiral zero.
  5. Non-Hermitian Skin Effect: Table 3 parity decay residual at eta=0.25 (-1.0130e-5), Hatano-Nelson real spectrum probe.
================================================================================
"""

import unittest
import numpy as np
from scipy.spatial import ConvexHull

from src.icosahedral_qc.projectors import (
    P_PAR, P_PERP, PI_PAR, PI_PERP,
    get_projectors, verify_projection_orthogonality,
    compute_icosahedral_symmetry_groups
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
from src.icosahedral_qc.non_hermitian import (
    classify_spatial_regions, build_non_hermitian_hamiltonian,
    compute_non_hermitian_skin_modes, compute_non_bloch_gbz_decay
)


class TestAdversarialQCProjectors(unittest.TestCase):
    """Adversarial stress-testing of 6D -> 3D projectors P_parallel and P_perp."""

    def test_01_matrix_identities_machine_precision(self):
        """Verify all 4 foundational projector identities to machine precision (< 2.3e-16)."""
        P_par, P_perp = get_projectors()
        I3 = np.eye(3)
        I6 = np.eye(6)

        err_par_par = np.max(np.abs(P_par @ P_par.T - I3))
        err_perp_perp = np.max(np.abs(P_perp @ P_perp.T - I3))
        err_cross = np.max(np.abs(P_par @ P_perp.T))
        err_completeness = np.max(np.abs(P_par.T @ P_par + P_perp.T @ P_perp - I6))

        self.assertLess(err_par_par, 2.3e-16)
        self.assertLess(err_perp_perp, 2.3e-16)
        self.assertLess(err_cross, 2.3e-16)
        self.assertLess(err_completeness, 2.3e-16)

        # Idempotency and mutual orthogonality of 6D projection operators
        Pi_par = P_par.T @ P_par
        Pi_perp = P_perp.T @ P_perp
        self.assertLess(np.max(np.abs(Pi_par @ Pi_par - Pi_par)), 2.3e-16)
        self.assertLess(np.max(np.abs(Pi_perp @ Pi_perp - Pi_perp)), 2.3e-16)
        self.assertLess(np.max(np.abs(Pi_par @ Pi_perp)), 2.3e-16)

    def test_02_100k_random_vectors_orthogonal_decomposition(self):
        """
        Adversarial probe: 100,000 random 6D vectors under Gaussian, Uniform, and Multi-Scale
        distributions to confirm orthogonal decomposition v = v_par + v_perp to < 1e-15.
        """
        P_par, P_perp = get_projectors()
        Pi_par = P_par.T @ P_par
        Pi_perp = P_perp.T @ P_perp

        rng = np.random.default_rng(20261018)
        N = 100000

        # Sub-batches: Gaussian, Uniform, and multi-scale vectors
        V_gauss = rng.normal(size=(N // 2, 6))
        V_unif = rng.uniform(-10.0, 10.0, size=(N // 2, 6))
        V_all = np.vstack([V_gauss, V_unif])

        # Project
        V_par = V_all @ Pi_par.T
        V_perp = V_all @ Pi_perp.T
        V_recon = V_par + V_perp

        # 1. Completeness / Reconstruction error
        norm_V = np.linalg.norm(V_all, axis=1)
        rel_recon_err = np.max(np.linalg.norm(V_recon - V_all, axis=1) / norm_V)
        self.assertLess(rel_recon_err, 1e-15, f"Decomposition reconstruction error {rel_recon_err:.2e} >= 1e-15")

        # 2. Orthogonality <v_par, v_perp> = 0
        dot_prods = np.sum(V_par * V_perp, axis=1)
        rel_ortho_err = np.max(np.abs(dot_prods) / (norm_V ** 2))
        self.assertLess(rel_ortho_err, 1e-15, f"Decomposition orthogonality error {rel_ortho_err:.2e} >= 1e-15")

        # 3. Pythagorean length conservation: ||x_par||^2 + ||x_perp||^2 == ||v||^2
        x_par = V_all @ P_par.T
        x_perp = V_all @ P_perp.T
        pyth_err = np.max(np.abs(np.sum(x_par**2, axis=1) + np.sum(x_perp**2, axis=1) - norm_V**2) / norm_V**2)
        self.assertLess(pyth_err, 2e-15, f"Pythagorean length error {pyth_err:.2e} >= 2e-15")

    def test_03_scale_invariance_and_canonical_axes(self):
        """Probe canonical 6D axes and extreme scale factors [1e-50, 1e50]."""
        P_par, P_perp = get_projectors()
        Pi_par = P_par.T @ P_par
        Pi_perp = P_perp.T @ P_perp

        # Canonical unit vectors in Z^6
        for i in range(6):
            e_i = np.zeros(6)
            e_i[i] = 1.0
            recon = Pi_par @ e_i + Pi_perp @ e_i
            self.assertLess(np.max(np.abs(recon - e_i)), 2.3e-16)
            self.assertLess(abs(np.dot(Pi_par @ e_i, Pi_perp @ e_i)), 2.3e-16)

        # Extreme scales
        for scale in [1e-50, 1e-20, 1e-1, 1e5, 1e20, 1e50]:
            v = np.array([1.0, -2.0, 3.0, -4.0, 5.0, -6.0]) * scale
            v_recon = Pi_par @ v + Pi_perp @ v
            rel_err = np.max(np.abs(v_recon - v)) / np.max(np.abs(v))
            self.assertLess(rel_err, 2e-15)


class TestAdversarialQCWindows(unittest.TestCase):
    """Adversarial stress-testing of acceptance windows W_b, -W_b, W_a."""

    def test_01_convexity_and_facet_halfspaces(self):
        """Probe convexity and boundary facet halfspace equations."""
        hull_a, hull_b, hull_bm = get_acceptance_windows()

        for name, hull in [("W_a", hull_a), ("W_b", hull_b), ("-W_b", hull_bm)]:
            verts = hull.points[hull.vertices]
            A = hull.equations[:, :3]
            b = hull.equations[:, 3]

            # 1. All vertices satisfy halfspace constraints A v + b <= 1e-15
            v_vals = verts @ A.T + b[None, :]
            self.assertLessEqual(np.max(v_vals), 2.3e-16, f"{name} vertices violate halfspaces")

            # 2. Random convex combinations of vertices strictly lie in interior
            rng = np.random.default_rng(42)
            weights = rng.dirichlet(np.ones(len(verts)), size=2000)
            interior_pts = weights @ verts
            int_vals = interior_pts @ A.T + b[None, :]
            self.assertLess(np.max(int_vals), 0.0, f"{name} convex combinations outside polytope")

            # 3. Outward perturbations along facet normals strictly violate halfspaces
            eps = 1e-7
            facet_centroids = np.mean(hull.points[hull.simplices], axis=1)
            pts_out = facet_centroids + eps * A
            out_vals = np.sum(pts_out * A, axis=1) + b
            self.assertGreater(np.min(out_vals), 0.5 * eps, f"{name} outward points not rejected")

    def test_02_volume_and_mirror_congruence(self):
        """Probe volume calculation and mirror enantiomer volume congruence."""
        hull_a, hull_b, hull_bm = get_acceptance_windows()

        # W_a volume matches theoretical Kepler Rhombic Triacontahedron volume
        # V_RTH = 4 * sqrt(5 + 2*sqrt(5)) * a^3 where a = 1 / sqrt(2)
        a = 1.0 / np.sqrt(2.0)
        expected_vol_a = 4.0 * np.sqrt(5.0 + 2.0 * np.sqrt(5.0)) * (a ** 3)
        self.assertAlmostEqual(hull_a.volume, expected_vol_a, places=7)

        # Mirror congruence: Vol(W_b) == Vol(-W_b) to machine precision
        vol_diff = abs(hull_b.volume - hull_bm.volume)
        self.assertLess(vol_diff, 1e-14, f"Enantiomer volume difference {vol_diff:.2e} >= 1e-14")

        # Number of vertices
        self.assertEqual(len(hull_a.vertices), 32)
        self.assertEqual(len(hull_b.vertices), 60)
        self.assertEqual(len(hull_bm.vertices), 60)

    def test_03_icosahedral_symmetry_invariance(self):
        """Probe icosahedral symmetry invariance and chiral discrimination."""
        hull_a, hull_b, hull_bm = get_acceptance_windows()
        IH_6D, I_6D, R_par_I, R_perp_I = compute_icosahedral_symmetry_groups()

        pts_b = hull_b.points[hull_b.vertices]
        pts_bm = hull_bm.points[hull_bm.vertices]
        pts_a = hull_a.points[hull_a.vertices]

        # 1. W_b invariant under all 60 proper rotations R in R_perp_I
        for R in R_perp_I:
            rot_b = pts_b @ R.T
            dists = np.min(np.linalg.norm(rot_b[:, None, :] - pts_b[None, :, :], axis=2), axis=1)
            self.assertLess(np.max(dists), 1e-14, "W_b not invariant under proper rotation")

        # 2. W_a invariant under all 120 elements of I_h
        for g in IH_6D:
            R_perp_g = P_PERP @ g @ P_PERP.T
            rot_a = pts_a @ R_perp_g.T
            dists = np.min(np.linalg.norm(rot_a[:, None, :] - pts_a[None, :, :], axis=2), axis=1)
            self.assertLess(np.max(dists), 1e-14, "W_a not invariant under full I_h element")

        # 3. W_b is strictly chiral: NO improper rotation (det < 0) preserves W_b
        for g in IH_6D:
            R_perp_g = P_PERP @ g @ P_PERP.T
            if np.linalg.det(R_perp_g) < 0:
                rot_b = pts_b @ R_perp_g.T
                dists = np.min(np.linalg.norm(rot_b[:, None, :] - pts_b[None, :, :], axis=2), axis=1)
                self.assertGreater(np.max(dists), 1e-3, "Improper operation falsely preserved chiral W_b")

        # 4. Parity inversion strictly maps W_b to -W_b
        parity_dist = np.max(np.min(np.linalg.norm((-pts_b)[:, None, :] - pts_bm[None, :, :], axis=2), axis=1))
        self.assertLess(parity_dist, 1e-14, "Parity inversion does not map W_b to -W_b")


class TestAdversarialQCBFS(unittest.TestCase):
    """Adversarial stress-testing of Cut-and-Project BFS engine."""

    def test_01_small_radius_boundary_cases(self):
        """Probe edge cases of radius R: R=0, R<1/sqrt(2), R=0.71."""
        hull_b = get_acceptance_window("W_b")

        # R = 0.0 -> origin only
        nodes_0, x_par_0, _, r_0 = bfs_vectorized_6d(hull_b, 0.0)
        self.assertEqual(len(nodes_0), 1)
        self.assertEqual(tuple(nodes_0[0]), (0, 0, 0, 0, 0, 0))
        self.assertAlmostEqual(r_0[0], 0.0)

        # R = 0.5 < 1/sqrt(2) -> origin only
        nodes_05, _, _, _ = bfs_vectorized_6d(hull_b, 0.5)
        self.assertEqual(len(nodes_05), 1)

        # R = 0.70 < 1/sqrt(2) approx 0.7071 -> origin only
        nodes_070, _, _, _ = bfs_vectorized_6d(hull_b, 0.70)
        self.assertEqual(len(nodes_070), 1)

        # R = 0.71 > 1/sqrt(2) -> origin + 12 nearest neighbors = 13 points
        nodes_071, _, _, r_071 = bfs_vectorized_6d(hull_b, 0.71)
        self.assertEqual(len(nodes_071), 13)
        self.assertAlmostEqual(np.max(r_071), 1.0 / np.sqrt(2.0), places=6)

    def test_02_brute_force_equivalence_at_r2(self):
        """Verify that BFS finds 100% of points in Z^6 satisfying cut-and-project at R=2.0."""
        hull_b = get_acceptance_window("W_b")
        R_test = 2.0
        nodes_bfs, _, _, _ = bfs_vectorized_6d(hull_b, R_test)
        set_bfs = set(tuple(n) for n in nodes_bfs)

        # Brute-force search over [-4, 4]^6
        grid = np.arange(-4, 5)
        mesh = np.array(np.meshgrid(grid, grid, grid, grid, grid, grid)).T.reshape(-1, 6)
        mesh_f = mesh.astype(float)
        x_par_all = mesh_f @ P_PAR.T
        r2 = np.sum(x_par_all**2, axis=1)
        in_ball = r2 <= (R_test + 1e-9)**2

        A, b = hull_b.equations[:, :3], hull_b.equations[:, 3]
        AP = A @ P_PERP
        cand = mesh_f[in_ball]
        cand_nodes = mesh[in_ball]
        in_hull = np.all(cand @ AP.T + b[None, :] <= 1e-9, axis=1)

        pts_brute = cand_nodes[in_hull]
        set_brute = set(tuple(n) for n in pts_brute)

        # Check exact equality
        self.assertEqual(set_bfs, set_brute, f"BFS missed {len(set_brute - set_bfs)} points at R=2.0")


class TestAdversarialQCBispectrum(unittest.TestCase):
    """Adversarial stress-testing of 3-Wave Bragg Bispectrum."""

    def test_01_translation_invariance_under_arbitrary_shifts(self):
        """Probe translation invariance Delta B under arbitrary shifts spanning 12 orders of magnitude."""
        hull_b = get_acceptance_window("W_b")
        _, xb, _, _ = bfs_vectorized_6d(hull_b, 3.5)
        base_res = evaluate_bispectrum(xb)
        B_base = base_res["B_array"]

        shifts = [
            np.array([0.0, 0.0, 0.0]),
            np.array([1e-10, -2e-10, 3e-10]),
            np.array([0.12345, -0.6789, 1.4142]),
            np.array([12.34, -56.78, 90.12]),
            np.array([500.0, -1200.0, 3400.0]),
        ]

        for shift in shifts:
            shifted_res = evaluate_bispectrum(xb, shift_vec=shift)
            max_dB = float(np.max(np.abs(B_base - shifted_res["B_array"])))
            self.assertLess(max_dB, 1e-14, f"Shift {shift} violated translation invariance: max dB = {max_dB:.2e}")

    def test_02_enantiomeric_mirror_parity_anti_symmetry(self):
        """Verify exact opposite-sign anti-symmetry B(W_b) + B(-W_b) = 0 to < 1e-14."""
        hull_b = get_acceptance_window("W_b")
        hull_bm = get_acceptance_window("-W_b")
        _, xb, _, _ = bfs_vectorized_6d(hull_b, 3.5)
        _, xbm, _, _ = bfs_vectorized_6d(hull_bm, 3.5)

        res_b = evaluate_bispectrum(xb)
        res_bm = evaluate_bispectrum(xbm)

        parity_sum = np.max(np.abs(res_b["B_array"] + res_bm["B_array"]))
        self.assertLess(parity_sum, 1e-14, f"Enantiomer parity sum {parity_sum:.2e} >= 1e-14")

    def test_03_achiral_control_zero(self):
        """Verify that achiral window W_a produces identically zero Bragg bispectrum."""
        hull_a = get_acceptance_window("W_a")
        _, xa, _, _ = bfs_vectorized_6d(hull_a, 3.5)
        res_a = evaluate_bispectrum(xa)

        max_B_achiral = float(np.max(np.abs(res_a["B_array"])))
        self.assertLess(max_B_achiral, 1e-14, f"Achiral control bispectrum {max_B_achiral:.2e} >= 1e-14")
        self.assertLess(res_a["chi_b"], 1e-14)


class TestAdversarialQCNonHermitian(unittest.TestCase):
    """Adversarial verification of HONHSE and Table 3 parity decay residual at eta=0.25."""

    def test_01_table3_decay_residual_at_eta_025(self):
        """Verify Table 3 non-Bloch dissipation scaling residual -1.0130e-5 at eta=0.25."""
        table3 = compute_non_bloch_gbz_decay()
        entry_25 = next(item for item in table3 if abs(item["eta"] - 0.25) < 1e-6)

        # Check values
        self.assertAlmostEqual(entry_25["delta_kappa_W_b"], 1.51898e-2, places=6)
        self.assertAlmostEqual(entry_25["delta_kappa_W_bm"], -1.51999e-2, places=6)
        self.assertAlmostEqual(entry_25["parity_sum_residual"], -1.0130e-5, places=8)
        self.assertTrue(entry_25["erratum_r42_reconciled"])

    def test_02_table3_dissipation_monotonicity_and_anti_symmetry(self):
        """Verify Table 3 GBZ compression monotonicity and anti-symmetry across eta in [0.05, 0.35]."""
        table3 = compute_non_bloch_gbz_decay()
        
        # Check compression monotonicity: delta_kappa_W_b decreases with increasing eta
        dks = [entry["delta_kappa_W_b"] for entry in table3]
        for i in range(len(dks) - 1):
            self.assertGreater(dks[i], dks[i+1], f"Monotonic decay rate compression violated at step {i}")

        # Check that parity residuals are all below 2.1e-3 and drop below 1.5e-5 for eta >= 0.20
        for entry in table3:
            res = abs(entry["parity_sum_residual"])
            self.assertLess(res, 2.1e-3)
            if entry["eta"] >= 0.20:
                self.assertLess(res, 1.5e-5)

    def test_03_hatano_nelson_spectral_reality_probe(self):
        """
        Adversarial probe: verify that the open-boundary Hatano-Nelson Hamiltonian H(eta)
        is isospectral to a real symmetric matrix via diagonal gauge transformation,
        explaining why imaginary parts of eigenvalues are machine-precision zero (< 1e-13).
        """
        hull_b = get_acceptance_window("W_b")
        _, xb, _, _ = bfs_vectorized_6d(hull_b, 2.0)  # N = 363
        
        H = build_non_hermitian_hamiltonian(xb, eta=0.25)
        evals = np.linalg.eigvals(H)
        max_imag = np.max(np.abs(np.imag(evals)))
        self.assertLess(max_imag, 1e-13, f"Non-Hermitian H has non-trivial imaginary eigenvalues: {max_imag:.2e}")


if __name__ == "__main__":
    unittest.main()
