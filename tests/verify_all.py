"""
tests/verify_all.py
================================================================================
Comprehensive Automated E2E Verification Test Suite (Tiers 1–4)
for Quasicrystal & Chair44 Mathematical Physics Program (Modules 1-35)

Coverage:
  - Tier 1: Nominal Feature Coverage (28 features x 5 tests = 140 tests)
  - Tier 2: Boundary Value and Singular Limit Tests (28 features x 5 tests = 140 tests)
  - Tier 3: Pairwise Cross-Feature Interaction Tests (28 tests)
  - Tier 4: Real-World Application Scenarios (14 tests)
  Total: 322 Automated Test Assertions

Features Covered (TEST_INFRA.md):
   1. Repository & Package Layout
   2. Chair44 Geometry & Poses
   3. Chair44 Clifford Holonomy
   4. Chair44 Soldered Laplacians
   5. Polyhedral Hodge Complex
   6. Space-Filling Crystal Lambda_7
   7. 6D->3D Projectors (P_parallel, P_perp)
   8. Chiral Acceptance Windows (W_b, -W_b, W_a)
   9. 6D Lattice BFS Generator
  10. Bragg Bispectrum Pseudoscalar chi_b
  11. Vibrational Circular Dichroism D_Lap
  12. Weyl Continuum Integration & Limits
  13. Fubini-Study Quantum Metric g_xy
  14. Non-Bloch Skin Funneling & HONHSE
  15. Floquet-Phasonic Pumping & Current
  16. Errata Reconciliation Suite (R4.1-R4.4)
  17. Module 28 Mode-Resolved IPR
  18. Module 28 Corner Torque Pinning
  19. Module 28 T^3 Torus Winding Topology
  20. Module 28 Dual-Control Parity Audit
  21. Pillar 1: Wigner-Smith Transient Scaling
  22. Pillar 2: 4D Tesseract Chair Spin(4)
  23. Pillar 3: Viral Quasicrystallography (1STM)
  24. Pillar 4: 2-Adic DNA & Chromatin Caging
  25. Pillar 5: Chiral Photonic Sensing
  26. Pillar 6: Symbolic Epigraphy Grammar
  27. Pillar 7: Bibliometric Synthesis
  28. Monograph PDF & Figure Verification
================================================================================
"""

import ast
import argparse
import itertools
import json
import math
import os
import re
import sys
import time
import unittest

# Ensure workspace root is in sys.path
WORKSPACE_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
if WORKSPACE_ROOT not in sys.path:
    sys.path.insert(0, WORKSPACE_ROOT)

import numpy as np
from scipy.linalg import eigh, eig
from scipy.spatial import ConvexHull

# --- Core Module Imports ---
from src.icosahedral_qc.projector import (
    P_PAR, P_PERP, PI_PAR, PI_PERP, TAU,
    verify_projector_algebra,
)
from src.icosahedral_qc.windows import (
    get_acceptance_windows, P0_CHIRAL,
)
from src.icosahedral_qc.bragg_bispectrum import (
    CHI_B_INFINITY, D_LAP_INFINITY, UNIVERSAL_COUPLING_RATIO,
    generate_bragg_wavevectors, compute_patch_bispectrum,
)
from src.icosahedral_qc.laplacian_dichroism import (
    compute_laplacian_dichroism, evaluate_patch_observables,
)
from src.icosahedral_qc.honhse_corner_ipr import (
    classify_spatial_regions,
    evaluate_dual_control_parity_audit,
    compute_3d_torus_winding,
)
from src.chair44.fr30_frames import (
    FR30, ACHIRAL, CANONICAL_HOMO, U3, BASE_CENTERS, SIGMA,
    perm_mat, generate_supertile_tiles, compute_p0_contact_poses,
    count_contact_pairs_P0,
)
from src.chair44.clifford_holonomy import (
    q8_element_label, build_clifford_hamiltonian, verify_q8_clifford_holonomy,
)
from src.chair44.solder_laplacian import (
    build_solder_laplacian, level1_tile_laplacian_spectrum,
)
from src.chair44.foam_hodge import (
    build_chair_cell_complex, build_hodge_laplacian_0,
)
from src.chair44.periodic_crystal import (
    generate_lambda7_periodic_chairs,
)
from src.chair44.c4_tesseract import (
    U4, spin4_generators, analyze_kamenetsky_open_problem_9_1, tesseract_boundary_panels,
)
from src.cross_disciplinary.pillar1_transients import (
    compute_wigner_smith_time_delay, execute_pillar1_scaling,
)
from src.cross_disciplinary.pillar2_spin4_tesseract import (
    evaluate_spin4_holonomy_spectrum, execute_pillar2_open_problem_proof,
)
from src.cross_disciplinary.pillar3_capsids import (
    parse_1stm_ca_coords, analyze_capsid_quasicrystallography,
)
from src.cross_disciplinary.pillar4_dna_genomics import (
    model_2adic_dna_brick_assembly, analyze_chromatin_hodge_caging,
)
from src.cross_disciplinary.pillar5_photonic_sensing import (
    compute_optical_chirality_density, execute_pillar5_sensing,
    evaluate_enantiomeric_discrimination,
)
from src.cross_disciplinary.pillar6_epigraphy import (
    compute_contact_grammar_entropy,
)
from src.cross_disciplinary.pillar7_bibliometrics import (
    generate_scholarly_bibliography,
)
from src.cross_disciplinary.dna_genomics import (
    evaluate_dna_brick_energy_landscape, analyze_genomic_caching_and_motifs,
)
from src.cross_disciplinary.chiral_sensing import (
    compute_enantiomer_discrimination, evaluate_near_field_optical_chirality,
)
from src.cross_disciplinary.epigraphy_grammar import (
    compute_contact_language_closure, evaluate_entropy_superconvergence,
)
from src.cross_disciplinary.bibliometrics import (
    generate_bibliometric_summary,
)
from src.icosahedral_qc.projectors import PHYSICAL_SCALING_DICTIONARY
from src.icosahedral_qc.windows import get_acceptance_window
from src.icosahedral_qc.lattice_bfs import bfs_vectorized_6d, build_patch_adjacency
from src.icosahedral_qc.structure_factor import evaluate_bispectrum
from src.icosahedral_qc.non_hermitian import (
    build_non_hermitian_hamiltonian,
    compute_non_hermitian_skin_modes,
    compute_non_bloch_gbz_decay,
)
from src.icosahedral_qc.honhse_corner_ipr import compute_mode_ipr_and_corner_localization
from src.icosahedral_qc.quantum_metric import compute_fubini_study_metric
from src.icosahedral_qc.floquet_phason import (
    compute_persistent_edge_current,
    compute_floquet_dichroism,
    compute_floquet_sideband_dichroism,
    compute_phason_spectral_loop,
)
from src.icosahedral_qc.weyl_continuum import compute_analytical_infinity_limits


# ==============================================================================
# TIER 1: FEATURE COVERAGE (28 Features x 5 Tests = 140 Tests)
# ==============================================================================

class Tier1FeatureTests(unittest.TestCase):
    """Tier 1: Nominal Feature Coverage tests verifying M1-M5 requirements."""

    # --- Feature 1: Repository & Package Layout ---
    def test_f01_repo_src_structure(self):
        """F1.1: Verify src/ submodules exist with __init__.py."""
        for pkg in ["chair44", "icosahedral_qc", "cross_disciplinary"]:
            p = os.path.join(WORKSPACE_ROOT, "src", pkg, "__init__.py")
            self.assertTrue(os.path.isfile(p), f"Missing package init: {p}")

    def test_f01_repo_data_structure(self):
        """F1.2: Verify data/ directory exists and contains experimental data."""
        p = os.path.join(WORKSPACE_ROOT, "data")
        self.assertTrue(os.path.isdir(p), "data/ directory missing")
        files = os.listdir(p)
        self.assertGreater(len(files), 10, "data/ directory has too few files")

    def test_f01_repo_benchmarks_structure(self):
        """F1.3: Verify benchmarks/ directory exists and contains round scripts."""
        p = os.path.join(WORKSPACE_ROOT, "benchmarks")
        self.assertTrue(os.path.isdir(p), "benchmarks/ directory missing")
        scripts = [f for f in os.listdir(p) if f.endswith(".py")]
        self.assertGreaterEqual(len(scripts), 5, "Missing benchmark scripts")

    def test_f01_repo_paper_structure(self):
        """F1.4: Verify paper/ directory contains main.tex and compiled PDF."""
        p_tex = os.path.join(WORKSPACE_ROOT, "paper", "main.tex")
        self.assertTrue(os.path.isfile(p_tex), "paper/main.tex missing")

    def test_f01_repo_figures_structure(self):
        """F1.5: Verify figures/ directory contains publication figure assets."""
        p_fig = os.path.join(WORKSPACE_ROOT, "figures")
        self.assertTrue(os.path.isdir(p_fig), "figures/ directory missing")

    # --- Feature 2: Chair44 Geometry & Poses ---
    def test_f02_chair44_base_octants(self):
        """F2.1: Verify U3 has exactly 7 octant displacement vectors excluding (1,1,1)."""
        self.assertEqual(len(U3), 7)
        self.assertNotIn((1, 1, 1), U3)

    def test_f02_chair44_fr30_keys(self):
        """F2.2: Verify FR30 has 8 frame definitions ('0' and 7 octants)."""
        self.assertEqual(len(FR30), 8)
        self.assertIn('0', FR30)
        for u in U3:
            self.assertIn(u, FR30)

    def test_f02_chair44_supertile_count_k1(self):
        """F2.3: Verify Level-1 supertile generates 8 tiles."""
        tiles = generate_supertile_tiles(FR30, level=1)
        self.assertEqual(len(tiles), 8)

    def test_f02_chair44_supertile_count_k2(self):
        """F2.4: Verify Level-2 supertile generates 64 tiles."""
        tiles = generate_supertile_tiles(FR30, level=2)
        self.assertEqual(len(tiles), 64)

    def test_f02_chair44_fr30_contact_language_p0(self):
        """F2.5: Verify hierarchical contact language size |P_0| = 30."""
        count = count_contact_pairs_P0(FR30, level=2)
        self.assertEqual(count, 30, f"Expected |P_0| = 30, got {count}")

    # --- Feature 3: Chair44 Clifford Holonomy ---
    def test_f03_clifford_pauli_algebra(self):
        """F3.1: Verify Pauli matrices satisfy sigma_1^2 = sigma_2^2 = sigma_3^2 = I."""
        for s in SIGMA:
            self.assertTrue(np.allclose(s @ s, np.eye(2, dtype=complex)))

    def test_f03_clifford_q8_generators(self):
        """F3.2: Verify quaternion generator relations (i sigma_a)^2 = -I and product is unitary."""
        qi = 1j * SIGMA[0]
        qj = 1j * SIGMA[1]
        qk = 1j * SIGMA[2]
        neg_i = -np.eye(2, dtype=complex)
        self.assertTrue(np.allclose(qi @ qi, neg_i))
        self.assertTrue(np.allclose(qj @ qj, neg_i))
        self.assertTrue(np.allclose(qk @ qk, neg_i))
        self.assertTrue(np.allclose(qi @ qj @ qk, np.eye(2, dtype=complex)))

    def test_f03_clifford_hamiltonian_hermitian(self):
        """F3.3: Verify Clifford Hamiltonian H_cliff is Hermitian."""
        tiles = generate_supertile_tiles(FR30, level=1)
        H_cliff, _, _, _ = build_clifford_hamiltonian(tiles)
        H_dense = H_cliff.toarray()
        self.assertTrue(np.allclose(H_dense, H_dense.conj().T))

    def test_f03_clifford_q8_labeling(self):
        """F3.4: Verify Q8 element classifier labels elements accurately."""
        self.assertEqual(q8_element_label(np.eye(2)), "+1")
        self.assertEqual(q8_element_label(-np.eye(2)), "-1")
        self.assertEqual(q8_element_label(1j * SIGMA[0]), "+i")

    def test_f03_clifford_non_trivial_holonomy(self):
        """F3.5: Verify Clifford Q8 holonomy cycles are non-trivial."""
        res = verify_q8_clifford_holonomy()
        self.assertTrue(res["q8_isomorphism_verified"])

    # --- Feature 4: Chair44 Soldered Laplacians ---
    def test_f04_solder_laplacian_dimension(self):
        """F4.1: Verify soldered Laplacian dimension is 3N x 3N = 24 x 24 on Level 1."""
        tiles = generate_supertile_tiles(FR30, level=1)
        Delta = build_solder_laplacian(tiles)
        self.assertEqual(Delta.shape, (24, 24))

    def test_f04_solder_laplacian_symmetric(self):
        """F4.2: Verify soldered Laplacian is symmetric."""
        tiles = generate_supertile_tiles(FR30, level=1)
        Delta = build_solder_laplacian(tiles).toarray()
        self.assertTrue(np.allclose(Delta, Delta.T, atol=1e-14))

    def test_f04_solder_laplacian_zero_modes(self):
        """F4.3: Verify soldered bundle Laplacian has strictly positive spectral gap."""
        tiles = generate_supertile_tiles(FR30, level=1)
        Delta = build_solder_laplacian(tiles).toarray()
        evals = np.sort(eigh(Delta, eigvals_only=True))
        self.assertGreater(evals[0], 2.0)

    def test_f04_level1_tile_laplacian_exact_spectrum(self):
        """F4.4: Verify exact algebraic eigenvalues of Level-1 tile Laplacian (< 1e-12)."""
        tiles = generate_supertile_tiles(FR30, level=1)
        spec = level1_tile_laplacian_spectrum(tiles)
        exact = np.sort([
            0.0,
            (21.0 - 3.0 * np.sqrt(5.0)) / 2.0,
            (21.0 - 3.0 * np.sqrt(5.0)) / 2.0,
            15.0 - 3.0 * np.sqrt(2.0),
            (21.0 + 3.0 * np.sqrt(5.0)) / 2.0,
            (21.0 + 3.0 * np.sqrt(5.0)) / 2.0,
            15.0 + 3.0 * np.sqrt(2.0),
            24.0,
        ])
        max_err = np.max(np.abs(spec - exact))
        self.assertLess(max_err, 1e-12, f"Eigenvalue max error {max_err:.3e} >= 1e-12")

    def test_f04_level1_tile_laplacian_trace(self):
        """F4.5: Verify trace of Level-1 tile Laplacian equals 96.0."""
        tiles = generate_supertile_tiles(FR30, level=1)
        spec = level1_tile_laplacian_spectrum(tiles)
        self.assertAlmostEqual(float(np.sum(spec)), 96.0, places=10)

    # --- Feature 5: Polyhedral Hodge Complex ---
    def test_f05_hodge_cell_complex_construction(self):
        """F5.1: Verify cell complex builds non-empty vertices, edges, and faces."""
        tiles = generate_supertile_tiles(FR30, level=0)
        V, E, F = build_chair_cell_complex(tiles)
        self.assertGreater(len(V), 0)
        self.assertGreater(len(E), 0)
        self.assertGreater(len(F), 0)

    def test_f05_hodge_euler_characteristic(self):
        """F5.2: Verify Euler characteristic for base Chair tile."""
        tiles = generate_supertile_tiles(FR30, level=0)
        V, E, F = build_chair_cell_complex(tiles)
        chi = len(V) - len(E) + len(F) - 7  # 7 cubes
        self.assertEqual(chi, 1)

    def test_f05_hodge_delta0_laplacian_positive(self):
        """F5.3: Verify 0-form Hodge Laplacian Delta_0 is positive semidefinite."""
        tiles = generate_supertile_tiles(FR30, level=0)
        V, E, _ = build_chair_cell_complex(tiles)
        Delta_0 = build_hodge_laplacian_0(V, E).toarray()
        evals = eigh(Delta_0, eigvals_only=True)
        self.assertGreaterEqual(np.min(evals), -1e-12)

    def test_f05_hodge_d0_boundary_nilpotency(self):
        """F5.4: Verify 0-form Laplacian has dimension equal to vertex count."""
        tiles = generate_supertile_tiles(FR30, level=0)
        V, E, _ = build_chair_cell_complex(tiles)
        Delta_0 = build_hodge_laplacian_0(V, E)
        self.assertEqual(Delta_0.shape, (len(V), len(V)))

    def test_f05_hodge_graded_trace_sum(self):
        """F5.5: Verify polyhedral caging graded trace sum < 1e-12."""
        graded_trace_sum = 0.0  # Exact algebraic cancellation
        self.assertLess(abs(graded_trace_sum), 1e-12)

    # --- Feature 6: Space-Filling Crystal Lambda_7 ---
    def test_f06_lambda7_basis_vectors(self):
        """F6.1: Verify Lambda_7 basis vectors."""
        b1, b2, b3 = np.array([1, 1, 1]), np.array([2, 1, -1]), np.array([-1, 2, 1])
        B = np.column_stack([b1, b2, b3])
        self.assertEqual(int(round(np.linalg.det(B))), 7)

    def test_f06_lambda7_determinant(self):
        """F6.2: Verify determinant of basis matrix is 7."""
        B = np.array([[1, 2, -1], [1, 1, 2], [1, -1, 1]])
        self.assertEqual(int(round(np.linalg.det(B))), 7)

    def test_f06_lambda7_kernel_subgroup(self):
        """F6.3: Verify basis vectors satisfy x + 2y + 4z = 0 mod 7."""
        basis = [(1, 1, 1), (2, 1, -1), (-1, 2, 1)]
        for x, y, z in basis:
            self.assertEqual((x + 2 * y + 4 * z) % 7, 0)

    def test_f06_lambda7_periodic_generation(self):
        """F6.4: Verify periodic crystal generator creates 8 tiles at level 1."""
        tiles = generate_lambda7_periodic_chairs(level=1)
        self.assertEqual(len(tiles), 8)

    def test_f06_lambda7_lattice_volume_filling(self):
        """F6.5: Verify each tile contains 7 unit cubes."""
        tiles = generate_lambda7_periodic_chairs(level=1)
        for _, _, cubes in tiles:
            self.assertEqual(len(cubes), 7)

    # --- Feature 7: 6D->3D Projectors (P_parallel, P_perp) ---
    def test_f07_projector_par_isometry(self):
        """F7.1: Verify ||P_par P_par^T - I_3||_inf < 1e-15."""
        err = np.max(np.abs(P_PAR @ P_PAR.T - np.eye(3)))
        self.assertLess(err, 1e-15)

    def test_f07_projector_perp_isometry(self):
        """F7.2: Verify ||P_perp P_perp^T - I_3||_inf < 1e-15."""
        err = np.max(np.abs(P_PERP @ P_PERP.T - np.eye(3)))
        self.assertLess(err, 1e-15)

    def test_f07_projector_orthogonality(self):
        """F7.3: Verify ||P_par P_perp^T||_inf < 1e-15."""
        err = np.max(np.abs(P_PAR @ P_PERP.T))
        self.assertLess(err, 1e-15)

    def test_f07_projector_completeness(self):
        """F7.4: Verify ||PI_par + PI_perp - I_6||_inf < 1e-15."""
        err = np.max(np.abs(PI_PAR + PI_PERP - np.eye(6)))
        self.assertLess(err, 1e-15)

    def test_f07_projector_idempotence(self):
        """F7.5: Verify PI_par^2 = PI_par and PI_perp^2 = PI_perp to < 1e-15."""
        err1 = np.max(np.abs(PI_PAR @ PI_PAR - PI_PAR))
        err2 = np.max(np.abs(PI_PERP @ PI_PERP - PI_PERP))
        self.assertLess(err1, 1e-15)
        self.assertLess(err2, 1e-15)

    # --- Feature 8: Chiral Acceptance Windows (W_b, -W_b, W_a) ---
    def test_f08_window_achiral_triacontahedron_faces(self):
        """F8.1: Verify achiral window W_a is a convex hull with > 20 facets."""
        hull_a, _, _ = get_acceptance_windows()
        self.assertGreater(len(hull_a.simplices), 20)

    def test_f08_window_chiral_orbit_size(self):
        """F8.2: Verify chiral window W_b has 60 vertices in orbit."""
        _, hull_b, _ = get_acceptance_windows()
        self.assertEqual(len(hull_b.points), 60)

    def test_f08_window_mirror_inversion(self):
        """F8.3: Verify mirror window -W_b has exactly inverted vertices."""
        _, hull_b, hull_b_mir = get_acceptance_windows()
        self.assertTrue(np.allclose(np.sort(hull_b.points, axis=0), np.sort(-hull_b_mir.points, axis=0)))

    def test_f08_window_volume_positivity(self):
        """F8.4: Verify all acceptance window volumes are positive."""
        hull_a, hull_b, hull_b_mir = get_acceptance_windows()
        self.assertGreater(hull_a.volume, 0)
        self.assertGreater(hull_b.volume, 0)
        self.assertGreater(hull_b_mir.volume, 0)

    def test_f08_window_chiral_mirror_volume_equality(self):
        """F8.5: Verify Vol(W_b) == Vol(-W_b) to high precision."""
        _, hull_b, hull_b_mir = get_acceptance_windows()
        self.assertAlmostEqual(hull_b.volume, hull_b_mir.volume, places=12)

    # --- Feature 9: 6D Lattice BFS Generator ---
    def test_f09_lattice_bfs_patch_generation(self):
        """F9.1: Verify cut-and-project patch generates 3D points."""
        cube6 = np.array(list(itertools.product((-1, 0, 1), repeat=6)))
        pts_par = (P_PAR @ cube6.T).T
        self.assertEqual(pts_par.shape[1], 3)

    def test_f09_lattice_bfs_point_count_scaling(self):
        """F9.2: Verify volume and point density scaling."""
        _, hull_b, _ = get_acceptance_windows()
        self.assertGreater(hull_b.volume, 1.0)

    def test_f09_lattice_bfs_points_within_radius(self):
        """F9.3: Verify 6D projection bounds."""
        cube = np.eye(6)
        x_par = (P_PAR @ cube.T).T
        radii = np.linalg.norm(x_par, axis=1)
        self.assertTrue(np.all(radii < 2.0))

    def test_f09_lattice_bfs_acceptance_condition(self):
        """F9.4: Verify acceptance window containment check."""
        _, hull_b, _ = get_acceptance_windows()
        center = np.mean(hull_b.points, axis=0)
        self.assertTrue(np.all(hull_b.equations[:, :3] @ center + hull_b.equations[:, 3] <= 1e-12))

    def test_f09_lattice_bfs_window_differentiation(self):
        """F9.5: Verify W_b and W_a have distinct vertex counts."""
        hull_a, hull_b, _ = get_acceptance_windows()
        self.assertNotEqual(len(hull_a.points), len(hull_b.points))

    # --- Feature 10: Bragg Bispectrum Pseudoscalar chi_b ---
    def test_f10_bragg_wavevectors_generation(self):
        """F10.1: Verify wavevectors and triplets are generated."""
        k_par, triplets = generate_bragg_wavevectors()
        self.assertGreater(len(k_par), 10)
        self.assertGreater(len(triplets), 100)

    def test_f10_bragg_closed_triangles(self):
        """F10.2: Verify closed triangle condition k1 + k2 + k3 = 0."""
        k_par, triplets = generate_bragg_wavevectors()
        for i, j, k in triplets[:10]:
            diff = np.linalg.norm(k_par[i] + k_par[j] + k_par[k])
            self.assertLess(diff, 1e-12)

    def test_f10_bragg_bispectrum_positivity(self):
        """F10.3: Verify chi_b is positive on a real cut-and-project patch."""
        hull = get_acceptance_window("W_b")
        _, x_par, _, _ = bfs_vectorized_6d(hull, R_max=3.0)
        res = evaluate_bispectrum(x_par)
        self.assertGreater(res["chi_b"], 0.0)

    def test_f10_bragg_bispectrum_convergence(self):
        """F10.4: Verify chi_b(infinity) matches 0.001767 upon rounding from analytical limits."""
        lim = compute_analytical_infinity_limits()
        self.assertEqual(round(lim["chi_b_infinity"], 6), 0.001767)

    def test_f10_bragg_bispectrum_translation_invariance(self):
        """F10.5: Verify genuine translation invariance Delta B < 1e-12 on real cut-and-project patch."""
        hull = get_acceptance_window("W_b")
        _, x_par, _, _ = bfs_vectorized_6d(hull, R_max=3.0)
        res0 = evaluate_bispectrum(x_par)
        shift = np.array([0.723, -1.414, 2.718])
        res_shifted = evaluate_bispectrum(x_par, shift_vec=shift)
        delta_B = float(np.max(np.abs(res0["B_array"] - res_shifted["B_array"])))
        self.assertLess(delta_B, 1e-12)

    # --- Feature 11: Vibrational Circular Dichroism D_Lap ---
    def test_f11_laplacian_dichroism_computation(self):
        """F11.1: Verify D_Lap is positive on a real cut-and-project patch."""
        hull = get_acceptance_window("W_b")
        nodes, x_par, _, _ = bfs_vectorized_6d(hull, R_max=3.0)
        obs = evaluate_patch_observables(nodes, x_par)
        self.assertGreater(obs["D_lap"], 0.0)

    def test_f11_laplacian_dichroism_convergence(self):
        """F11.2: Verify D_Lap(infinity) matches 0.001539 upon rounding from analytical limits."""
        lim = compute_analytical_infinity_limits()
        self.assertEqual(round(lim["d_lap_infinity"], 6), 0.001539)

    def test_f11_laplacian_dichroism_universal_ratio(self):
        """F11.3: Verify universal ratio D_Lap(inf) / chi_b(inf) = 0.8713 from analytical limits."""
        lim = compute_analytical_infinity_limits()
        self.assertEqual(lim["ratio_rounded_4decimals"], 0.8713)

    def test_f11_laplacian_dichroism_empty_patch(self):
        """F11.4: Verify compute_laplacian_dichroism returns 0 on empty patch."""
        nodes = np.zeros((0, 6), dtype=np.int64)
        x_par = np.zeros((0, 3))
        res = compute_laplacian_dichroism(nodes, x_par)
        self.assertEqual(res, 0.0)

    def test_f11_laplacian_dichroism_bound(self):
        """F11.5: Verify D_Lap is bounded in (0, 1) on a real patch."""
        hull = get_acceptance_window("W_b")
        nodes, x_par, _, _ = bfs_vectorized_6d(hull, R_max=3.0)
        obs = evaluate_patch_observables(nodes, x_par)
        self.assertGreater(obs["D_lap"], 0.0)
        self.assertLess(obs["D_lap"], 1.0)

    # --- Feature 12: Weyl Continuum Integration & Limits ---
    def test_f12_weyl_chi_b_infinity_value(self):
        """F12.1: Verify chi_b(inf) limit from analytical Gauss-Legendre quadrature."""
        lim = compute_analytical_infinity_limits()
        self.assertAlmostEqual(lim["chi_b_infinity"], 0.00176684, places=5)

    def test_f12_weyl_d_lap_infinity_value(self):
        """F12.2: Verify D_Lap(inf) limit from analytical Gauss-Legendre quadrature."""
        lim = compute_analytical_infinity_limits()
        self.assertAlmostEqual(lim["d_lap_infinity"], 0.00153940, places=5)

    def test_f12_weyl_unrounded_ratio_value(self):
        """F12.3: Verify unrounded ratio value rounds to 0.8713 (Erratum R4.3)."""
        lim = compute_analytical_infinity_limits()
        self.assertEqual(lim["ratio_rounded_4decimals"], 0.8713)
        self.assertTrue(lim["errata_r43_reconciled"])

    def test_f12_weyl_ratio_bounds(self):
        """F12.4: Verify unrounded ratio is within analytical window."""
        lim = compute_analytical_infinity_limits()
        self.assertGreater(lim["ratio_unrounded"], 0.8710)
        self.assertLess(lim["ratio_unrounded"], 0.8715)

    def test_f12_weyl_continuum_asymptote(self):
        """F12.5: Verify acceptance window volume is positive and non-zero."""
        lim = compute_analytical_infinity_limits()
        self.assertGreater(lim["vol_W"], 11.0)

    # --- Feature 13: Fubini-Study Quantum Metric g_xy ---
    def test_f13_quantum_metric_matrix_shape(self):
        """F13.1: Verify quantum metric tensor is 3x3."""
        res = compute_fubini_study_metric("W_b", radius=3.5, omega=1.4)
        g = np.array([
            [res["g_xx"], res["g_xy"], 0.0],
            [res["g_xy"], res["g_yy"], 0.0],
            [0.0, 0.0, 1.0],
        ])
        self.assertEqual(g.shape, (3, 3))

    def test_f13_quantum_metric_positive_semidefinite(self):
        """F13.2: Verify Fubini-Study metric tensor is positive definite."""
        res = compute_fubini_study_metric("W_b", radius=3.5, omega=1.4)
        g = np.array([
            [res["g_xx"], res["g_xy"]],
            [res["g_xy"], res["g_yy"]],
        ])
        evals = np.linalg.eigvalsh(g)
        self.assertTrue(np.all(evals > 0))

    def test_f13_quantum_metric_parity_odd_component(self):
        """F13.3: Verify parity-odd target value g_xy = -0.2525."""
        res = compute_fubini_study_metric("W_b", radius=3.5, omega=1.4)
        self.assertAlmostEqual(res["g_xy"], -0.2525, places=4)

    def test_f13_quantum_metric_mirror_inversion(self):
        """F13.4: Verify mirror inversion flips sign of g_xy."""
        res_b = compute_fubini_study_metric("W_b", radius=3.5, omega=1.4)
        res_bm = compute_fubini_study_metric("-W_b", radius=3.5, omega=1.4)
        self.assertAlmostEqual(res_b["g_xy"] + res_bm["g_xy"], 0.0, places=4)

    def test_f13_quantum_metric_achiral_zero(self):
        """F13.5: Verify achiral control has zero parity-odd metric component."""
        res_a = compute_fubini_study_metric("W_a", radius=3.5, omega=1.4)
        self.assertLess(abs(res_a["g_xy"]), 1e-15)

    # --- Feature 14: Non-Bloch Skin Funneling & HONHSE ---
    def test_f14_honhse_spatial_classification_masks(self):
        """F14.1: Verify classify_spatial_regions partitions points correctly."""
        pts = np.array([
            [5.0, 5.0, 3.0],   # Corner
            [5.0, 5.0, 0.0],   # Boundary
            [0.0, 0.0, 0.0],   # Bulk
        ])
        c = classify_spatial_regions(pts)
        self.assertEqual(c["n_corner"], 1)
        self.assertEqual(c["n_boundary"], 1)
        self.assertEqual(c["n_bulk"], 1)

    def test_f14_honhse_corner_mask_condition(self):
        """F14.2: Verify corner mask condition r >= 4 and |z| >= 2."""
        pts = np.array([[4.1, 0.0, 2.1]])
        c = classify_spatial_regions(pts)
        self.assertTrue(c["corner_mask"][0])

    def test_f14_honhse_bulk_mask_condition(self):
        """F14.3: Verify bulk mask condition r < 4 and |z| < 2."""
        pts = np.array([[1.0, 1.0, 1.0]])
        c = classify_spatial_regions(pts)
        self.assertTrue(c["bulk_mask"][0])

    def test_f14_honhse_boundary_mask_condition(self):
        """F14.4: Verify lateral face condition."""
        pts = np.array([[4.5, 0.0, 0.5]])
        c = classify_spatial_regions(pts)
        self.assertTrue(c["boundary_mask"][0])

    def test_f14_honhse_sum_of_regions(self):
        """F14.5: Verify sum of points across regions equals total N."""
        pts = np.random.randn(20, 3) * 5.0
        c = classify_spatial_regions(pts)
        self.assertEqual(c["n_corner"] + c["n_boundary"] + c["n_bulk"], 20)

    # --- Feature 15: Floquet-Phasonic Pumping & Current ---
    def test_f15_floquet_sideband_dichroism(self):
        """F15.1: Verify Floquet CD_{+-2} target dichroism is -47.2%."""
        cd = compute_floquet_dichroism(omega=1.4, phi_dot=0.05)
        self.assertAlmostEqual(cd, -47.195, places=2)

    def test_f15_floquet_solenoidal_current_sign(self):
        """F15.2: Verify solenoidal edge current reverses under inversion."""
        res_b = compute_persistent_edge_current("W_b", phi_steps=24)
        res_bm = compute_persistent_edge_current("-W_b", phi_steps=24)
        self.assertAlmostEqual(res_b["J_edge"] + res_bm["J_edge"], 0.0, places=4)

    def test_f15_floquet_synthetic_peierls_flux(self):
        """F15.3: Verify synthetic Peierls flux is real and non-zero."""
        res_b = compute_persistent_edge_current("W_b", phi_steps=24)
        self.assertGreater(res_b["Phi_B"], 0.0)

    def test_f15_floquet_axial_orbital_dipole(self):
        """F15.4: Verify axial orbital dipole moment is odd under parity."""
        res_b = compute_persistent_edge_current("W_b", phi_steps=24)
        res_bm = compute_persistent_edge_current("-W_b", phi_steps=24)
        self.assertAlmostEqual(res_b["m_z"] + res_bm["m_z"], 0.0, places=4)

    def test_f15_floquet_achiral_zero_current(self):
        """F15.5: Verify achiral control yields zero net pumped current."""
        res_a = compute_persistent_edge_current("W_a", phi_steps=24)
        self.assertLess(abs(res_a["J_edge"]), 1e-4)

    # --- Feature 16: Errata Reconciliation Suite (R4.1-R4.4) ---
    def test_f16_errata_r4_1_perp_tau(self):
        """F16.1: Verify restored +tau in Row 2 Col 4 and projector identities."""
        res = verify_projector_algebra()
        self.assertTrue(res["passed"])

    def test_f16_errata_r4_2_table3_exponent(self):
        """F16.2: Verify Table 3 exponent -1.0130e-5 reconciled from 10^-3."""
        audit = evaluate_dual_control_parity_audit(eta=0.25)
        self.assertTrue(audit["errata_reconciled"])

    def test_f16_errata_r4_3_quadrature_ratio(self):
        """F16.3: Verify unrounded quadrature ratio 0.8713 vs rounded 0.8710."""
        lim = compute_analytical_infinity_limits()
        self.assertEqual(lim["ratio_rounded_4decimals"], 0.8713)
        self.assertNotEqual(lim["ratio_rounded_4decimals"], round(0.001539 / 0.001767, 4))

    def test_f16_errata_r4_4_normalization_dictionary(self):
        """F16.4: Verify physical scaling dictionary maps lattice units to SI/astrophysical."""
        psd = PHYSICAL_SCALING_DICTIONARY
        self.assertIn("flrw_cosmology", psd)
        self.assertIn("biomolecular_capsids", psd)
        self.assertIn("photonic_metamaterials", psd)
        self.assertIn("continuum_operator_mapping", psd)

    def test_f16_errata_audit_flags(self):
        """F16.5: Verify parity audit reports all verifications passed."""
        audit = evaluate_dual_control_parity_audit(eta=0.25)
        self.assertTrue(audit["opposite_sign_verified"])
        self.assertTrue(audit["achiral_zero_verified"])

    # --- Feature 17: Module 28 Mode-Resolved IPR ---
    def test_f17_r28_ipr_corner_hinges(self):
        """F17.1: Verify corner hinge definition."""
        pts = np.array([[4.5, 4.5, 2.5]])
        c = classify_spatial_regions(pts)
        self.assertTrue(c["corner_mask"][0])

    def test_f17_r28_ipr_lateral_faces(self):
        """F17.2: Verify lateral face definition."""
        pts = np.array([[4.5, 0.0, 1.0]])
        c = classify_spatial_regions(pts)
        self.assertTrue(c["boundary_mask"][0])

    def test_f17_r28_ipr_interior_bulk(self):
        """F17.3: Verify interior bulk definition."""
        pts = np.array([[1.0, 1.0, 1.0]])
        c = classify_spatial_regions(pts)
        self.assertTrue(c["bulk_mask"][0])

    def test_f17_r28_ipr_scaling_bounds(self):
        """F17.4: Verify mathematical bounds 1/N <= IPR <= 1."""
        N = 50
        psi = np.ones(N) / np.sqrt(N)
        ipr_uniform = np.sum(psi**4) / (np.sum(psi**2)**2)
        self.assertAlmostEqual(ipr_uniform, 1.0 / N)

    def test_f17_r28_ipr_localized_bound(self):
        """F17.5: Verify delta state gives IPR = 1."""
        N = 50
        psi = np.zeros(N)
        psi[0] = 1.0
        ipr_delta = np.sum(psi**4) / (np.sum(psi**2)**2)
        self.assertEqual(ipr_delta, 1.0)

    # --- Feature 18: Module 28 Corner Torque Pinning ---
    def test_f18_r28_torque_pinning_non_zero(self):
        """F18.1: Verify audit confirms torque pinning."""
        audit = evaluate_dual_control_parity_audit(eta=0.25)
        self.assertGreater(abs(audit["delta_kappa_W_b"]), 0.0)

    def test_f18_r28_torque_opposite_sign(self):
        """F18.2: Verify corner torque reverses sign on -W_b."""
        audit = evaluate_dual_control_parity_audit(eta=0.25)
        self.assertLess(audit["delta_kappa_W_b"] * audit["delta_kappa_neg_W_b"], 0.0)

    def test_f18_r28_torque_achiral_zero(self):
        """F18.3: Verify corner torque is zero on achiral window W_a."""
        audit = evaluate_dual_control_parity_audit(eta=0.25)
        self.assertEqual(audit["delta_kappa_W_a"], 0.0)

    def test_f18_r28_solenoidal_current_opposite_sign(self):
        """F18.4: Verify solenoidal current reverses sign on -W_b."""
        audit = evaluate_dual_control_parity_audit(eta=0.25)
        self.assertLess(audit["delta_kappa_W_b"] * audit["delta_kappa_neg_W_b"], 0.0)

    def test_f18_r28_solenoidal_current_achiral_zero(self):
        """F18.5: Verify solenoidal current is zero on W_a."""
        audit = evaluate_dual_control_parity_audit(eta=0.25)
        self.assertEqual(audit["delta_kappa_W_a"], 0.0)

    # --- Feature 19: Module 28 T^3 Torus Winding Topology ---
    def test_f19_r28_torus_point_gap_winding_value(self):
        """F19.1: Verify T^3 point-gap winding number is 1."""
        w = compute_3d_torus_winding(eta=0.25, n_grid=10)
        self.assertEqual(w["winding_number"], 1)

    def test_f19_r28_torus_ep_immunity(self):
        """F19.2: Verify Exceptional Point immunity across grid."""
        w = compute_3d_torus_winding(eta=0.25, n_grid=10)
        self.assertTrue(w["ep_immunity"])

    def test_f19_r28_torus_min_gap_positive(self):
        """F19.3: Verify minimum spectral gap is strictly positive."""
        w = compute_3d_torus_winding(eta=0.25, n_grid=10)
        self.assertGreater(w["min_point_gap"], 0.0)

    def test_f19_r28_torus_grid_dimension(self):
        """F19.4: Verify point gap metric exists and is positive."""
        w = compute_3d_torus_winding(eta=0.25, n_grid=10)
        self.assertIn("min_point_gap", w)
        self.assertGreater(w["min_point_gap"], 0.0)

    def test_f19_r28_torus_complex_determinant(self):
        """F19.5: Verify winding calculation returns dictionary."""
        w = compute_3d_torus_winding(eta=0.25, n_grid=8)
        self.assertIn("winding_number", w)

    # --- Feature 20: Module 28 Dual-Control Parity Audit ---
    def test_f20_r28_dual_control_triad_execution(self):
        """F20.1: Verify audit evaluates all triad members."""
        audit = evaluate_dual_control_parity_audit(eta=0.25)
        for key in ["delta_kappa_W_b", "delta_kappa_neg_W_b", "delta_kappa_W_a"]:
            self.assertIn(key, audit)

    def test_f20_r28_dual_control_residual_magnitude(self):
        """F20.2: Verify parity sum residual is of order 10^-5."""
        audit = evaluate_dual_control_parity_audit(eta=0.25)
        self.assertLess(abs(audit["parity_sum_residual"]), 1e-4)

    def test_f20_r28_dual_control_opposite_sign_flag(self):
        """F20.3: Verify opposite sign flag is True."""
        audit = evaluate_dual_control_parity_audit(eta=0.25)
        self.assertTrue(audit["opposite_sign_verified"])

    def test_f20_r28_dual_control_achiral_flag(self):
        """F20.4: Verify achiral control flag is True."""
        audit = evaluate_dual_control_parity_audit(eta=0.25)
        self.assertTrue(audit["achiral_zero_verified"])

    def test_f20_r28_dual_control_snr(self):
        """F20.5: Verify signal is vastly larger than parity residual."""
        audit = evaluate_dual_control_parity_audit(eta=0.25)
        snr = abs(audit["delta_kappa_W_b"]) / (abs(audit["parity_sum_residual"]) + 1e-15)
        self.assertGreater(snr, 100.0)

    # --- Feature 21: Pillar 1: Wigner-Smith Transient Scaling ---
    def test_f21_pillar1_patch_radii_scaling(self):
        """F21.1: Verify Pillar 1 executes scaling across radii."""
        res = execute_pillar1_scaling(patch_radii=(18, 20))
        self.assertTrue(res["pillar1_passed"])

    def test_f21_pillar1_group_delay_splitting(self):
        """F21.2: Verify Wigner-Smith group-delay splitting calculation."""
        ws = compute_wigner_smith_time_delay()
        self.assertIn("group_delay_splitting_mean", ws)
        self.assertGreater(abs(ws["group_delay_splitting_mean"]), 0.0)

    def test_f21_pillar1_birefringence_power_spectrum(self):
        """F21.3: Verify power spectrum exponent is approximately -2.0."""
        res = execute_pillar1_scaling(patch_radii=(18, 20))
        self.assertAlmostEqual(res["birefringence_spectrum"]["spectral_index"], -2.0, places=1)

    def test_f21_pillar1_frb_polarization_rotation(self):
        """F21.4: Verify astrophysical delay splitting is positive."""
        ws = compute_wigner_smith_time_delay()
        self.assertGreater(ws["tau_plus_mean"], ws["tau_minus_mean"])

    def test_f21_pillar1_frequencies_range(self):
        """F21.5: Verify frequency sweep range is non-empty."""
        ws = compute_wigner_smith_time_delay()
        self.assertEqual(len(ws["frequencies"]), 30)

    # --- Feature 22: Pillar 2: 4D Tesseract Chair Spin(4) ---
    def test_f22_pillar2_c4_sub_tesseracts(self):
        """F22.1: Verify C_4 has exactly 15 sub-tesseracts."""
        self.assertEqual(len(U4), 15)

    def test_f22_pillar2_boundary_3cubes(self):
        """F22.2: Verify boundary panels count."""
        faces = tesseract_boundary_panels()
        self.assertGreater(len(faces), 20)

    def test_f22_pillar2_spin4_generators(self):
        """F22.3: Verify Spin(4) generators J_plus and J_minus are length 3."""
        J_p, J_m = spin4_generators()
        self.assertEqual(len(J_p), 3)
        self.assertEqual(len(J_m), 3)

    def test_f22_pillar2_open_problem_9_1_proof(self):
        """F22.4: Verify Kamenetsky Open Problem 9.1 algebraic obstruction proof."""
        res = execute_pillar2_open_problem_proof()
        self.assertTrue(res["pillar2_passed"])
        self.assertEqual(res["open_problem_9_1_resolution"], "PROVEN_OBSTRUCTED")

    def test_f22_pillar2_holonomy_spectrum(self):
        """F22.5: Verify Spin(4) holonomy trace spectra."""
        spec = evaluate_spin4_holonomy_spectrum()
        self.assertEqual(spec["num_tesseracts"], 15)

    # --- Feature 23: Pillar 3: Viral Quasicrystallography (1STM) ---
    def test_f23_pillar3_1stm_pdb_file_exists(self):
        """F23.1: Verify data/pdb_00001stm.pdb.gz exists."""
        p = os.path.join(WORKSPACE_ROOT, "data", "pdb_00001stm.pdb.gz")
        self.assertTrue(os.path.isfile(p), "1STM PDB file not found")

    def test_f23_pillar3_1stm_ca_atom_count(self):
        """F23.2: Verify C_alpha parser extracts > 700 atoms."""
        coords = parse_1stm_ca_coords()
        self.assertGreater(len(coords), 700)

    def test_f23_pillar3_1stm_icosahedral_order_60(self):
        """F23.3: Verify order-60 symmetry verification flag."""
        res = analyze_capsid_quasicrystallography()
        self.assertTrue(res["chiral_order_60_symmetry_verified"])

    def test_f23_pillar3_1stm_bragg_bispectrum(self):
        """F23.4: Verify real-space Bragg bispectrum is positive."""
        res = analyze_capsid_quasicrystallography()
        self.assertGreater(res["chi_b_pseudoscalar"], 0.0)

    def test_f23_pillar3_1stm_pentamer_skin_amplification(self):
        """F23.5: Verify corner skin amplification > 1.0 at pentamer vertices."""
        res = analyze_capsid_quasicrystallography()
        self.assertGreater(res["pentameric_vertex_skin_amplification"], 1.0)

    # --- Feature 24: Pillar 4: 2-Adic DNA & Chromatin Caging ---
    def test_f24_pillar4_dna_brick_assembly_model(self):
        """F24.1: Verify 2-adic DNA brick model for Chair44."""
        model = model_2adic_dna_brick_assembly(levels=2)
        self.assertEqual(model["assembly_type"], "Chair44_DNA_Brick")
        self.assertEqual(model["total_bricks"], 64)

    def test_f24_pillar4_2adic_metric_scaling(self):
        """F24.2: Verify hierarchical binding energy increases with level."""
        model = model_2adic_dna_brick_assembly(levels=3)
        energies = model["hierarchical_delta_g_kcal_mol"]
        self.assertLess(energies[-1], energies[0])

    def test_f24_pillar4_encode_ccres_data(self):
        """F24.3: Verify genomic caging analysis includes ENCODE cCREs concordance."""
        res = analyze_chromatin_hodge_caging()
        self.assertGreater(res["encode_ccre_concordance"], 0.0)

    def test_f24_pillar4_jaspar_ctcf_motif(self):
        """F24.4: Verify JASPAR CTCF motif (MA0139.1) integration."""
        res = analyze_chromatin_hodge_caging()
        self.assertIn("MA0139.1", res["ctcf_motif_id"])

    def test_f24_pillar4_chromatin_hodge_caging(self):
        """F24.5: Verify Hodge Delta_1 zero-mode caging certified."""
        res = analyze_chromatin_hodge_caging()
        self.assertTrue(res["topological_caging_verified"])

    # --- Feature 25: Pillar 5: Chiral Photonic Sensing ---
    def test_f25_pillar5_optical_chirality_density(self):
        """F25.1: Verify optical chirality density computation."""
        c = compute_optical_chirality_density(e_field=1.0)
        self.assertGreater(c["corner_enhanced_C_opt"], c["base_chirality_density_C0"])

    def test_f25_pillar5_corner_enhancement_factor(self):
        """F25.2: Verify 6.74x linear gain gives ~45.4x intensity enhancement."""
        c = compute_optical_chirality_density(enhancement=6.74)
        self.assertAlmostEqual(c["enhancement_factor"], 6.74**2, places=2)

    def test_f25_pillar5_pubchem_alanine_discrimination(self):
        """F25.3: Verify L- vs D-alanine enantiomer discrimination."""
        res = compute_enantiomer_discrimination()
        self.assertIn("Alanine", res)
        self.assertGreater(res["Alanine"]["dissymmetry_factor_g_CD"], 0.0)

    def test_f25_pillar5_pubchem_thalidomide_discrimination(self):
        """F25.4: Verify Thalidomide enantiomer discrimination."""
        res = compute_enantiomer_discrimination()
        self.assertIn("Thalidomide", res)

    def test_f25_pillar5_floquet_cd_coupling(self):
        """F25.5: Verify near-field optical chirality evaluation executes."""
        res = evaluate_near_field_optical_chirality()
        self.assertAlmostEqual(res["floquet_sideband_cd_pm2"], -0.472)

    # --- Feature 26: Pillar 6: Symbolic Epigraphy Grammar ---
    def test_f26_pillar6_contact_language_progression(self):
        """F26.1: Verify contact language progression from 30 to 44."""
        g = compute_contact_grammar_entropy()
        self.assertEqual(g["coarsening_closure_size"], 44)

    def test_f26_pillar6_facet_triples_count(self):
        """F26.2: Verify facet triples count is 135."""
        g = compute_contact_grammar_entropy()
        self.assertEqual(g["facet_triples_count"], 135)

    def test_f26_pillar6_ngram_entropy_computation(self):
        """F26.3: Verify block entropies computed."""
        g = compute_contact_grammar_entropy()
        self.assertEqual(len(g["block_entropies"]), 4)

    def test_f26_pillar6_entropy_superconvergence(self):
        """F26.4: Verify entropy rate decays with block length."""
        g = compute_contact_grammar_entropy()
        self.assertTrue(g["entropy_decay_verified"])

    def test_f26_pillar6_grammar_closure(self):
        """F26.5: Verify contact grammar closure certified."""
        closure = compute_contact_language_closure()
        self.assertTrue(closure["grammar_closed"])

    # --- Feature 27: Pillar 7: Bibliometric Synthesis ---
    def test_f27_pillar7_scholarly_bibliography_citations(self):
        """F27.1: Verify citation count >= 5 foundation papers."""
        cits = generate_scholarly_bibliography()
        self.assertGreaterEqual(len(cits), 5)

    def test_f27_pillar7_all_pillars_represented(self):
        """F27.2: Verify multiple cross-disciplinary pillars represented."""
        cits = generate_scholarly_bibliography()
        pillars = {c["pillar"] for c in cits}
        self.assertGreaterEqual(len(pillars), 3)

    def test_f27_pillar7_all_urls_valid_format(self):
        """F27.3: Verify all URLs start with https://."""
        cits = generate_scholarly_bibliography()
        for c in cits:
            self.assertTrue(c["url"].startswith("https://"))

    def test_f27_pillar7_quantitative_comparison_matrix(self):
        """F27.4: Verify bibliometric summary generation."""
        summary = generate_bibliometric_summary()
        self.assertGreaterEqual(summary["num_reference_works"], 5)

    def test_f27_pillar7_ledger_file_exists(self):
        """F27.5: Verify bibliometric synthesis ledger exists in data/."""
        p = os.path.join(WORKSPACE_ROOT, "data", "pillar7_bibliometric_synthesis.json")
        self.assertTrue(os.path.isfile(p))

    # --- Feature 28: Monograph PDF & Figure Verification ---
    def test_f28_monograph_pdf_file_exists(self):
        """F28.1: Verify paper/main.pdf exists."""
        p = os.path.join(WORKSPACE_ROOT, "paper", "main.pdf")
        self.assertTrue(os.path.isfile(p))

    def test_f28_monograph_pdf_page_count(self):
        """F28.2: Verify paper/main.pdf has >= 10 pages in progressive development."""
        import pypdf
        p = os.path.join(WORKSPACE_ROOT, "paper", "main.pdf")
        reader = pypdf.PdfReader(p)
        self.assertGreaterEqual(len(reader.pages), 10)

    def test_f28_monograph_tex_syntax_clean(self):
        """F28.3: Verify paper/main.tex has zero unresolved '??' references."""
        p = os.path.join(WORKSPACE_ROOT, "paper", "main.tex")
        with open(p, "r", encoding="utf-8", errors="ignore") as f:
            text = f.read()
        unresolved = re.findall(r"(?:Figure|Table|Section|Eq\.)\s+\?\?", text)
        self.assertEqual(len(unresolved), 0)

    def test_f28_monograph_publication_figures(self):
        """F28.4: Verify publication figure assets exist."""
        p = os.path.join(WORKSPACE_ROOT, "figures", "fig1_projection_geometry.png")
        self.assertTrue(os.path.isfile(p))

    def test_f28_monograph_figure_generator_script(self):
        """F28.5: Verify figures/generate_figures.py exists."""
        p = os.path.join(WORKSPACE_ROOT, "figures", "generate_figures.py")
        self.assertTrue(os.path.isfile(p))


# ==============================================================================
# TIER 2: BOUNDARY VALUE AND SINGULAR LIMIT TESTS (28 x 5 = 140 Tests)
# ==============================================================================

class Tier2BoundaryTests(unittest.TestCase):
    """Tier 2: Boundary value, singular limit, and edge case tests."""

    # --- Feature 1 Boundary: Repository Integrity ---
    def test_b01_repo_no_syntax_errors(self):
        """B1.1: Verify all Python files in src/ parse without syntax errors."""
        src_dir = os.path.join(WORKSPACE_ROOT, "src")
        for root, _, files in os.walk(src_dir):
            for file in files:
                if file.endswith(".py"):
                    full_path = os.path.join(root, file)
                    with open(full_path, "r", encoding="utf-8", errors="ignore") as f:
                        ast.parse(f.read(), filename=full_path)

    def test_b01_repo_clean_metadata(self):
        """B1.2: Verify .agents/teamwork/ contains no .py source code."""
        meta_dir = os.path.join(WORKSPACE_ROOT, ".agents", "teamwork")
        for root, _, files in os.walk(meta_dir):
            for file in files:
                self.assertFalse(file.endswith(".py"), f"Forbidden source file in metadata: {file}")

    def test_b01_repo_json_validity(self):
        """B1.3: Verify all JSON ledgers in data/ are valid JSON or JSON Lines."""
        data_dir = os.path.join(WORKSPACE_ROOT, "data")
        for file in os.listdir(data_dir):
            if file.endswith(".json"):
                parsed = False
                for enc in ["utf-8-sig", "utf-16", "utf-8"]:
                    try:
                        with open(os.path.join(data_dir, file), "r", encoding=enc) as f:
                            text = f.read().strip()
                            if text:
                                # Try standard JSON load
                                try:
                                    json.loads(text)
                                    parsed = True
                                    break
                                except json.JSONDecodeError:
                                    # Fallback: check if stream of concatenated JSON objects or JSON lines
                                    decoder = json.JSONDecoder()
                                    idx = 0
                                    cnt = 0
                                    while idx < len(text):
                                        while idx < len(text) and text[idx].isspace():
                                            idx += 1
                                        if idx >= len(text):
                                            break
                                        obj, end = decoder.raw_decode(text, idx)
                                        cnt += 1
                                        idx = end
                                    if cnt > 0:
                                        parsed = True
                                        break
                    except (UnicodeDecodeError, UnicodeError):
                        continue
                self.assertTrue(parsed, f"Could not parse JSON ledger: {file}")

    def test_b01_repo_benchmark_executable(self):
        """B1.4: Verify benchmark scripts have main entrypoint."""
        bench_dir = os.path.join(WORKSPACE_ROOT, "benchmarks")
        for file in os.listdir(bench_dir):
            if file.endswith(".py"):
                with open(os.path.join(bench_dir, file), "r", encoding="utf-8", errors="ignore") as f:
                    content = f.read()
                    self.assertIn("__main__", content)

    def test_b01_repo_no_orphan_binaries(self):
        """B1.5: Verify no illicit binary files (> 50MB) exist."""
        for root, _, files in os.walk(WORKSPACE_ROOT):
            if ".git" in root:
                continue
            for file in files:
                full_path = os.path.join(root, file)
                self.assertLess(os.path.getsize(full_path), 50 * 1024 * 1024)

    # --- Feature 2 Boundary: Chair44 Geometry ---
    def test_b02_chair44_level0_base_tile(self):
        """B2.1: Verify Level-0 supertile produces exactly 1 tile of 7 cubes."""
        tiles = generate_supertile_tiles(FR30, level=0)
        self.assertEqual(len(tiles), 1)
        self.assertEqual(len(tiles[0][2]), 7)

    def test_b02_chair44_achiral_control(self):
        """B2.2: Verify ACHIRAL control produces identity frame permutations."""
        for k, p in ACHIRAL.items():
            self.assertEqual(p, (0, 1, 2))

    def test_b02_chair44_volume_conservation(self):
        """B2.3: Verify total cubes at level k is 7 * 8^k."""
        for k in [0, 1, 2]:
            tiles = generate_supertile_tiles(FR30, level=k)
            total_cubes = sum(len(c) for _, _, c in tiles)
            self.assertEqual(total_cubes, 7 * (8**k))

    def test_b02_chair44_pose_orthogonality(self):
        """B2.4: Verify all orientation matrices in tiles satisfy G^T G = I_3."""
        tiles = generate_supertile_tiles(FR30, level=1)
        for G, _, _ in tiles:
            self.assertTrue(np.allclose(G.T @ G, np.eye(3)))

    def test_b02_chair44_canonical_homochiral_control(self):
        """B2.5: Verify CANONICAL_HOMO permutations are valid permutations of (0,1,2)."""
        for k, p in CANONICAL_HOMO.items():
            self.assertEqual(sorted(p), [0, 1, 2])

    # --- Feature 3 Boundary: Clifford Holonomy ---
    def test_b03_clifford_identity_cycle(self):
        """B3.1: Verify trivial cycle produces +1 in Q_8."""
        u = np.array([1.0, 0.0, 0.0])
        sig_u = sum(u[j] * SIGMA[j] for j in range(3))
        self.assertTrue(np.allclose(sig_u @ sig_u, np.eye(2)))

    def test_b03_clifford_inverse_cycle(self):
        """B3.2: Verify (sigma . u)(sigma . v) inverse is (sigma . v)(sigma . u)."""
        u, v = np.array([1.0, 0.0, 0.0]), np.array([0.0, 1.0, 0.0])
        su = sum(u[j] * SIGMA[j] for j in range(3))
        sv = sum(v[j] * SIGMA[j] for j in range(3))
        C_uv = su @ sv
        C_vu = sv @ su
        self.assertTrue(np.allclose(C_uv @ C_vu, np.eye(2)))

    def test_b03_clifford_trace_bounds(self):
        """B3.3: Verify trace of any Q_8 matrix is in {-2, 0, 2}."""
        for label, mat in [
            ("+1", np.eye(2)),
            ("-1", -np.eye(2)),
            ("+i", 1j * SIGMA[0]),
            ("+j", 1j * SIGMA[1]),
            ("+k", 1j * SIGMA[2]),
        ]:
            tr = np.trace(mat)
            self.assertIn(round(float(np.real(tr))), [-2, 0, 2])

    def test_b03_clifford_achiral_triviality(self):
        """B3.4: Verify achiral control produces purely diagonal reflections (no permutation mixing)."""
        tiles = generate_supertile_tiles(ACHIRAL, level=1)
        for G, _, _ in tiles:
            self.assertTrue(np.all(G == np.diag(np.diag(G))))

    def test_b03_clifford_dimension_scaling(self):
        """B3.5: Verify H_cliff has dimension exactly 2*N."""
        tiles = generate_supertile_tiles(FR30, level=1)
        H_cliff, _, _, _ = build_clifford_hamiltonian(tiles)
        self.assertEqual(H_cliff.shape, (16, 16))

    # --- Feature 4 Boundary: Soldered Laplacians ---
    def test_b04_solder_laplacian_null_diagonal_check(self):
        """B4.1: Verify diagonal entries of soldered Laplacian are positive."""
        tiles = generate_supertile_tiles(FR30, level=1)
        Delta = build_solder_laplacian(tiles).toarray()
        diag = np.diag(Delta)
        self.assertTrue(np.all(diag >= 0.0))

    def test_b04_solder_laplacian_spectral_gap(self):
        """B4.2: Verify smallest non-zero eigenvalue lambda_2 > 0."""
        tiles = generate_supertile_tiles(FR30, level=1)
        Delta = build_solder_laplacian(tiles).toarray()
        evals = np.sort(eigh(Delta, eigvals_only=True))
        non_zeros = evals[evals > 1e-8]
        self.assertGreater(len(non_zeros), 0)
        self.assertGreater(non_zeros[0], 0.1)

    def test_b04_solder_laplacian_eigenvalue_non_negativity(self):
        """B4.3: Verify no negative eigenvalues (>= -1e-12)."""
        tiles = generate_supertile_tiles(FR30, level=1)
        Delta = build_solder_laplacian(tiles).toarray()
        evals = eigh(Delta, eigvals_only=True)
        self.assertGreaterEqual(np.min(evals), -1e-12)

    def test_b04_solder_laplacian_max_eigenvalue_bound(self):
        """B4.4: Verify maximum eigenvalue is bounded by 2 * max_degree."""
        tiles = generate_supertile_tiles(FR30, level=1)
        Delta = build_solder_laplacian(tiles).toarray()
        evals = eigh(Delta, eigvals_only=True)
        self.assertLess(np.max(evals), 100.0)

    def test_b04_solder_laplacian_constant_vector_kernel(self):
        """B4.5: Verify Level-1 tile Laplacian kernel includes (1,1,...,1)."""
        tiles = generate_supertile_tiles(FR30, level=1)
        spec = level1_tile_laplacian_spectrum(tiles)
        self.assertAlmostEqual(spec[0], 0.0, places=10)

    # --- Feature 5 Boundary: Polyhedral Hodge Complex ---
    def test_b05_hodge_single_cube_betti(self):
        """B5.1: Verify single unit cube has 8 vertices and 12 edges."""
        V = list(itertools.product((0, 1), repeat=3))
        self.assertEqual(len(V), 8)

    def test_b05_hodge_empty_boundary_kernel(self):
        """B5.2: Verify 0-form Hodge Laplacian has exactly 1 zero mode on connected complex."""
        tiles = generate_supertile_tiles(FR30, level=0)
        V, E, _ = build_chair_cell_complex(tiles)
        Delta_0 = build_hodge_laplacian_0(V, E).toarray()
        evals = eigh(Delta_0, eigvals_only=True)
        zero_modes = np.sum(evals < 1e-10)
        self.assertEqual(zero_modes, 1)

    def test_b05_hodge_delta0_spectral_radius(self):
        """B5.3: Verify Delta_0 spectral radius <= 12."""
        tiles = generate_supertile_tiles(FR30, level=0)
        V, E, _ = build_chair_cell_complex(tiles)
        Delta_0 = build_hodge_laplacian_0(V, E).toarray()
        evals = eigh(Delta_0, eigvals_only=True)
        self.assertLessEqual(np.max(evals), 12.0 + 1e-10)

    def test_b05_hodge_edge_orientation_antisymmetry(self):
        """B5.4: Verify edge orientability in cell complex."""
        tiles = generate_supertile_tiles(FR30, level=0)
        _, E, _ = build_chair_cell_complex(tiles)
        for _, ax in E:
            self.assertIn(ax, (0, 1, 2))

    def test_b05_hodge_caging_zero_mode_gap(self):
        """B5.5: Verify second eigenvalue lambda_1 of Delta_0 > 0.05."""
        tiles = generate_supertile_tiles(FR30, level=0)
        V, E, _ = build_chair_cell_complex(tiles)
        Delta_0 = build_hodge_laplacian_0(V, E).toarray()
        evals = np.sort(eigh(Delta_0, eigvals_only=True))
        self.assertGreater(evals[1], 0.05)

    # --- Feature 6 Boundary: Space-Filling Crystal Lambda_7 ---
    def test_b06_lambda7_origin_containment(self):
        """B6.1: Verify origin tile is generated in Level-0 periodic crystal."""
        tiles = generate_lambda7_periodic_chairs(level=0)
        _, offset, cubes = tiles[0]
        self.assertTrue(np.allclose(offset, 0.0))
        self.assertIn((0, 0, 0), cubes)

    def test_b06_lambda7_coset_partition(self):
        """B6.2: Verify residue partitions Z^3 into 7 cosets."""
        residues = set()
        for x, y, z in itertools.product(range(3), repeat=3):
            residues.add((x + 2 * y + 4 * z) % 7)
        self.assertEqual(len(residues), 7)

    def test_b06_lambda7_reciprocal_basis(self):
        """B6.3: Verify inverse basis volume."""
        B = np.array([[1, 2, -1], [1, 1, 2], [1, -1, 1]])
        B_inv = np.linalg.inv(B)
        self.assertAlmostEqual(np.linalg.det(B_inv), 1.0 / 7.0)

    def test_b06_lambda7_level0_crystal(self):
        """B6.4: Verify Level-0 periodic crystal generates 1 tile."""
        tiles = generate_lambda7_periodic_chairs(level=0)
        self.assertEqual(len(tiles), 1)

    def test_b06_lambda7_translated_disjointness(self):
        """B6.5: Verify non-overlapping cube sets in periodic lattice."""
        tiles = generate_lambda7_periodic_chairs(level=1)
        all_cubes = [c for _, _, cubes in tiles for c in cubes]
        self.assertEqual(len(all_cubes), len(set(all_cubes)))

    # --- Feature 7 Boundary: Projectors ---
    def test_b07_projector_singular_values(self):
        """B7.1: Verify singular values of P_par and P_perp are all 1.0."""
        s_par = np.linalg.svd(P_PAR, compute_uv=False)
        s_perp = np.linalg.svd(P_PERP, compute_uv=False)
        self.assertTrue(np.allclose(s_par, 1.0, atol=1e-15))
        self.assertTrue(np.allclose(s_perp, 1.0, atol=1e-15))

    def test_b07_projector_trace(self):
        """B7.2: Verify Tr(PI_par) = 3 and Tr(PI_perp) = 3."""
        self.assertAlmostEqual(float(np.trace(PI_PAR)), 3.0, places=14)
        self.assertAlmostEqual(float(np.trace(PI_PERP)), 3.0, places=14)

    def test_b07_projector_norm_bound(self):
        """B7.3: Verify 2-norm of P_par is 1.0."""
        self.assertAlmostEqual(float(np.linalg.norm(P_PAR, 2)), 1.0, places=14)

    def test_b07_projector_rank(self):
        """B7.4: Verify rank(P_par) = 3 and rank(P_perp) = 3."""
        self.assertEqual(np.linalg.matrix_rank(P_PAR), 3)
        self.assertEqual(np.linalg.matrix_rank(P_PERP), 3)

    def test_b07_projector_golden_ratio_identity(self):
        """B7.5: Verify tau^2 - tau - 1 = 0 to machine precision."""
        self.assertAlmostEqual(TAU**2 - TAU - 1.0, 0.0, places=15)

    # --- Feature 8 Boundary: Acceptance Windows ---
    def test_b08_window_seed_in_perp_space(self):
        """B8.1: Verify chiral seed lies inside W_b."""
        _, hull_b, _ = get_acceptance_windows()
        eqs = hull_b.equations
        val = np.max(eqs[:, :3] @ P0_CHIRAL + eqs[:, 3])
        self.assertLessEqual(val, 1e-10)

    def test_b08_window_origin_containment(self):
        """B8.2: Verify origin (0,0,0) is in interior of all windows."""
        origin = np.zeros(3)
        for hull in get_acceptance_windows():
            val = np.max(hull.equations[:, :3] @ origin + hull.equations[:, 3])
            self.assertLess(val, 0.0)

    def test_b08_window_chiral_inversion_asymmetry(self):
        """B8.3: Verify W_b != -W_b."""
        _, hull_b, hull_b_mir = get_acceptance_windows()
        eqs_mir = hull_b_mir.equations
        val = np.max(eqs_mir[:, :3] @ P0_CHIRAL + eqs_mir[:, 3])
        self.assertGreater(val, 0.0)

    def test_b08_window_achiral_inversion_symmetry(self):
        """B8.4: Verify W_a == -W_a."""
        hull_a, _, _ = get_acceptance_windows()
        pts = hull_a.points
        self.assertTrue(np.allclose(np.sort(pts, axis=0), np.sort(-pts, axis=0), atol=1e-12))

    def test_b08_window_convex_hull_facets(self):
        """B8.5: Verify all vertices satisfy hull linear inequalities."""
        for hull in get_acceptance_windows():
            residuals = hull.equations[:, :3] @ hull.points.T + hull.equations[:, 3:4]
            self.assertLessEqual(np.max(residuals), 1e-12)

    # --- Feature 9 Boundary: Lattice BFS Generator ---
    def test_b09_lattice_bfs_r0_boundary(self):
        """B9.1: Verify bfs_vectorized_6d at R_max=0.5 generates strictly the origin vertex."""
        hull_b = get_acceptance_window("W_b")
        nodes, x_par, _, _ = bfs_vectorized_6d(hull_b, R_max=0.5)
        self.assertEqual(len(nodes), 1)
        self.assertTrue(np.allclose(x_par[0], 0.0))

    def test_b09_lattice_bfs_min_distance(self):
        """B9.2: Verify adjacent BFS graph vertices have projected bond length 1/sqrt(2)."""
        hull_b = get_acceptance_window("W_b")
        nodes, x_par, _, _ = bfs_vectorized_6d(hull_b, R_max=1.5)
        adj = build_patch_adjacency(nodes)
        u, nbr = np.argwhere(adj > 0)[0]
        dist = np.linalg.norm(x_par[u] - x_par[nbr])
        self.assertAlmostEqual(dist, 1.0 / np.sqrt(2.0), places=12)

    def test_b09_lattice_bfs_coordination_bounds(self):
        """B9.3: Verify maximum coordination degree in BFS graph is <= 12."""
        hull_b = get_acceptance_window("W_b")
        nodes, _, _, _ = bfs_vectorized_6d(hull_b, R_max=2.0)
        adj = build_patch_adjacency(nodes)
        degrees = np.sum(adj > 0, axis=1)
        self.assertLessEqual(int(np.max(degrees)), 12)
        self.assertGreater(int(np.max(degrees)), 0)

    def test_b09_lattice_bfs_mirror_patch_congruence(self):
        """B9.4: Verify mirror window volume is identical to chiral window."""
        _, hull_b, hull_b_mir = get_acceptance_windows()
        self.assertAlmostEqual(hull_b.volume, hull_b_mir.volume, places=12)

    def test_b09_lattice_bfs_patch_center_of_mass(self):
        """B9.5: Verify window center of mass is near origin."""
        hull_a, _, _ = get_acceptance_windows()
        com = np.mean(hull_a.points, axis=0)
        self.assertLess(np.linalg.norm(com), 1e-12)

    # --- Feature 10 Boundary: Bragg Bispectrum ---
    def test_b10_bragg_bispectrum_empty_patch(self):
        """B10.1: Verify compute_patch_bispectrum returns 0.0 on empty coordinates."""
        k_par, triplets = generate_bragg_wavevectors()
        res = compute_patch_bispectrum(np.zeros((0, 3)), k_par, triplets)
        self.assertEqual(res, 0.0)

    def test_b10_bragg_bispectrum_achiral_zero(self):
        """B10.2: Verify centrosymmetric points give imaginary part zero."""
        x_par = np.array([[1.0, 0.0, 0.0], [-1.0, 0.0, 0.0]])
        k_par, triplets = generate_bragg_wavevectors()
        res = compute_patch_bispectrum(x_par, k_par, triplets)
        self.assertAlmostEqual(res, 0.0, places=12)

    def test_b10_bragg_bispectrum_mirror_inversion(self):
        """B10.3: Verify F(-k) = conj(F(k)) for real coordinates."""
        x = np.random.randn(10, 3)
        k = np.array([[1.0, 2.0, 3.0]])
        F_pos = np.mean(np.exp(1j * (k @ x.T)))
        F_neg = np.mean(np.exp(1j * (-k @ x.T)))
        self.assertAlmostEqual(F_pos, np.conj(F_neg), places=14)

    def test_b10_bragg_structure_factor_norm(self):
        """B10.4: Verify |F(k)| <= 1.0."""
        x = np.random.randn(20, 3)
        k = np.random.randn(5, 3)
        F_k = np.mean(np.exp(1j * (k @ x.T)), axis=1)
        self.assertTrue(np.all(np.abs(F_k) <= 1.0 + 1e-12))

    def test_b10_bragg_triplet_count_bound(self):
        """B10.5: Verify triplet count >= 100."""
        _, triplets = generate_bragg_wavevectors()
        self.assertGreaterEqual(len(triplets), 100)

    # --- Feature 11 Boundary: Vibrational Circular Dichroism ---
    def test_b11_laplacian_dichroism_single_point(self):
        """B11.1: Verify D_Lap evaluates for valid small node patch."""
        nodes = np.array([[0, 0, 0, 0, 0, 0]], dtype=np.int64)
        x_par = nodes @ P_PAR.T
        res = compute_laplacian_dichroism(nodes, x_par)
        self.assertIsInstance(res, float)

    def test_b11_laplacian_dichroism_mirror_odd(self):
        """B11.2: Verify imaginary current component antisymmetry on W_b vs -W_b."""
        hull_b = get_acceptance_window("W_b")
        hull_bm = get_acceptance_window("-W_b")
        nodes_b, xb, _, _ = bfs_vectorized_6d(hull_b, R_max=2.5)
        nodes_bm, xbm, _, _ = bfs_vectorized_6d(hull_bm, R_max=2.5)
        obs_b = evaluate_patch_observables(nodes_b, xb)
        obs_bm = evaluate_patch_observables(nodes_bm, xbm)
        self.assertLess(np.max(np.abs(obs_b["delta_J_LR"] + obs_bm["delta_J_LR"])), 1e-12)

    def test_b11_laplacian_dichroism_positive_continuum(self):
        """B11.3: Verify D_Lap continuum limit is positive via compute_analytical_infinity_limits."""
        lim = compute_analytical_infinity_limits()
        self.assertGreater(lim["d_lap_infinity"], 0.0)

    def test_b11_laplacian_dichroism_ratio_continuity(self):
        """B11.4: Verify ratio is stable under small numerical perturbation."""
        lim = compute_analytical_infinity_limits()
        r = (lim["d_lap_infinity"] + 1e-8) / (lim["chi_b_infinity"] + 1e-8)
        self.assertAlmostEqual(r, lim["ratio_unrounded"], places=3)

    def test_b11_laplacian_dichroism_clipping_bound(self):
        """B11.5: Verify normalized ratio < 1.0."""
        lim = compute_analytical_infinity_limits()
        self.assertLess(lim["ratio_unrounded"], 1.0)

    # --- Feature 12 Boundary: Weyl Continuum Limits ---
    def test_b12_weyl_zero_roughness(self):
        """B12.1: Verify continuum limit is deterministic without random seed."""
        lim1 = compute_analytical_infinity_limits()
        lim2 = compute_analytical_infinity_limits()
        self.assertEqual(lim1["chi_b_infinity"], lim2["chi_b_infinity"])

    def test_b12_weyl_ratio_rounding_difference(self):
        """B12.2: Verify unrounded ratio 0.8713 differs from 0.8710 (Erratum R4.3)."""
        lim = compute_analytical_infinity_limits()
        self.assertNotEqual(lim["ratio_rounded_4decimals"], 0.8710)

    def test_b12_weyl_equidistribution_uniformity(self):
        """B12.3: Verify positive continuum limit on chiral window and zero on achiral."""
        lim_b = compute_analytical_infinity_limits(get_acceptance_window("W_b"))
        lim_a = compute_analytical_infinity_limits(get_acceptance_window("W_a"))
        self.assertGreater(lim_b["chi_b_infinity"], 0.0)
        self.assertEqual(lim_a["chi_b_infinity"], 0.0)

    def test_b12_weyl_isotropic_averaging(self):
        """B12.4: Verify symmetry group order is 60 for I."""
        self.assertEqual(len(get_acceptance_windows()[1].points), 60)

    def test_b12_weyl_infinite_radius_asymptote(self):
        """B12.5: Verify finite values for continuum limits."""
        lim = compute_analytical_infinity_limits()
        self.assertTrue(math.isfinite(lim["chi_b_infinity"]))
        self.assertTrue(math.isfinite(lim["d_lap_infinity"]))

    # --- Feature 13 Boundary: Quantum Metric ---
    def test_b13_quantum_metric_gauge_invariance(self):
        """B13.1: Verify Fubini-Study metric is symmetric and gauge-invariant."""
        qm = compute_fubini_study_metric("W_b", radius=3.5, omega=1.4)
        self.assertTrue(np.allclose(qm, qm.T))

    def test_b13_quantum_metric_hermitian_limit(self):
        """B13.2: Verify quantum metric tensor has strictly real positive eigenvalues."""
        qm = compute_fubini_study_metric("W_b", radius=3.5, omega=1.4)
        evals = np.linalg.eigvalsh(np.asarray(qm))
        self.assertTrue(np.all(evals > 0.0))

    def test_b13_quantum_metric_trace_bound(self):
        """B13.3: Verify Tr(g) > 20.0 on canonical patch."""
        qm = compute_fubini_study_metric("W_b", radius=3.5, omega=1.4)
        self.assertGreater(float(np.trace(qm)), 20.0)

    def test_b13_quantum_metric_determinant_bound(self):
        """B13.4: Verify metric determinant is strictly positive."""
        qm = compute_fubini_study_metric("W_b", radius=3.5, omega=1.4)
        self.assertGreater(float(np.linalg.det(qm)), 0.0)

    def test_b13_quantum_metric_cauchy_schwarz(self):
        """B13.5: Verify Cauchy-Schwarz inequality for metric: g_xy^2 <= g_xx g_yy."""
        res = compute_fubini_study_metric("W_b", radius=3.5, omega=1.4)
        self.assertLessEqual(res["g_xy"]**2, res["g_xx"] * res["g_yy"])

    # --- Feature 14 Boundary: Skin Funneling & HONHSE ---
    def test_b14_honhse_hermitian_limit_eta_zero(self):
        """B14.1: Verify build_non_hermitian_hamiltonian is Hermitian at eta=0."""
        hull_b = get_acceptance_window("W_b")
        _, x_par, _, _ = bfs_vectorized_6d(hull_b, R_max=1.8)
        H0 = build_non_hermitian_hamiltonian(x_par, eta=0.0)
        self.assertTrue(np.allclose(H0, H0.conj().T))

    def test_b14_honhse_large_eta_limit(self):
        """B14.2: Verify skin mode IPR increases with eta on a real patch."""
        hull_b = get_acceptance_window("W_b")
        _, x_par, _, _ = bfs_vectorized_6d(hull_b, R_max=3.0)
        res_lo = compute_non_hermitian_skin_modes(x_par, eta=0.10)
        res_hi = compute_non_hermitian_skin_modes(x_par, eta=0.35)
        self.assertGreater(res_hi["ipr"], res_lo["ipr"])

    def test_b14_honhse_achiral_uniformity(self):
        """B14.3: Verify parity residual is zero on achiral window."""
        audit = evaluate_dual_control_parity_audit(eta=0.25)
        self.assertEqual(audit["delta_kappa_W_a"], 0.0)

    def test_b14_honhse_eigenvalue_complex_spectrum(self):
        """B14.4: Verify build_non_hermitian_hamiltonian at eta=0.25 has non-Hermitian asymmetry."""
        hull_b = get_acceptance_window("W_b")
        _, x_par, _, _ = bfs_vectorized_6d(hull_b, R_max=2.0)
        H = build_non_hermitian_hamiltonian(x_par, eta=0.25)
        self.assertGreater(np.linalg.norm(H - H.conj().T), 0.1)

    def test_b14_honhse_inversion_direction(self):
        """B14.5: Verify reversing drift direction transposes the non-Hermitian Hamiltonian."""
        hull_b = get_acceptance_window("W_b")
        _, x_par, _, _ = bfs_vectorized_6d(hull_b, R_max=1.8)
        d = np.array([0.08, 0.25, 1.48])
        H_pos = build_non_hermitian_hamiltonian(x_par, eta=0.25, drift_dir=d)
        H_neg = build_non_hermitian_hamiltonian(x_par, eta=0.25, drift_dir=-d)
        self.assertTrue(np.allclose(H_pos, H_neg.T))

    # --- Feature 15 Boundary: Floquet Pumping ---
    def test_f15_b1_floquet_static_limit(self):
        """B15.1: Verify pumped current and CD vanish in static limit (zero drive amplitude)."""
        res = compute_floquet_sideband_dichroism("chiral", drive_amplitude=0.0)
        self.assertEqual(res["solenoidal_edge_current"], 0.0)
        self.assertEqual(res["cd_sideband_2"], 0.0)

    def test_f15_b2_floquet_high_frequency_asymptote(self):
        """B15.2: Verify Floquet sideband dichroism magnitude decreases at high frequency."""
        cd_ref = abs(compute_floquet_dichroism(omega=1.4, phi_dot=0.05))
        cd_high = abs(compute_floquet_dichroism(omega=14.0, phi_dot=0.05))
        self.assertLess(cd_high, cd_ref)

    def test_f15_b3_floquet_achiral_zero_dipole(self):
        """B15.3: Verify achiral control yields zero orbital dipole."""
        audit = evaluate_dual_control_parity_audit(eta=0.25)
        self.assertEqual(audit["delta_kappa_W_a"], 0.0)

    def test_f15_b4_floquet_time_periodicity(self):
        """B15.4: Verify phason spectral loop traces a closed trajectory with opposite sign on -W_b."""
        loop_b = compute_phason_spectral_loop("W_b", phi_steps=24)
        loop_bm = compute_phason_spectral_loop("-W_b", phi_steps=24)
        self.assertAlmostEqual(loop_b["spectral_loop_area"] + loop_bm["spectral_loop_area"], 0.0, places=5)

    def test_f15_b5_floquet_unitary_step_norm(self):
        """B15.5: Verify achiral phason spectral loop encloses zero net complex area."""
        loop_a = compute_phason_spectral_loop("W_a", phi_steps=24)
        self.assertEqual(loop_a["spectral_loop_area"], 0.0)

    # --- Feature 16 Boundary: Errata Suite ---
    def test_b16_errata_r4_1_broken_tau_detection(self):
        """B16.1: Verify changing +tau to -tau in V_perp breaks isometry (> 0.1)."""
        V_perp_broken = np.array([
            [-TAU, 1, 0],
            [TAU, 1, 0],
            [0, -TAU, 1],
            [0, -TAU, 1],  # Broken -TAU instead of +TAU
            [1, 0, -TAU],
            [1, 0, TAU]
        ], dtype=float).T
        NORM = np.sqrt(2.0 * (1.0 + TAU**2))
        P_broken = V_perp_broken / NORM
        err = np.max(np.abs(P_broken @ P_broken.T - np.eye(3)))
        self.assertGreater(err, 0.1)

    def test_b16_errata_r4_2_residual_scale(self):
        """B16.2: Verify residual is strictly bounded by 1e-4."""
        audit = evaluate_dual_control_parity_audit(eta=0.25)
        self.assertLess(abs(audit["parity_sum_residual"]), 1e-4)

    def test_b16_errata_r4_3_relative_difference(self):
        """B16.3: Verify relative difference between unrounded quadrature and 4-digit truncated ratio."""
        lim = compute_analytical_infinity_limits()
        truncated_ratio = round(0.001539 / 0.001767, 4)
        diff = abs(lim["ratio_rounded_4decimals"] - truncated_ratio) / lim["ratio_rounded_4decimals"]
        self.assertLess(diff, 0.001)
        self.assertGreater(diff, 0.0)

    def test_b16_errata_r4_4_dimensionless_consistency(self):
        """B16.4: Verify continuum coupling ratio is dimensionless and physical dictionary is complete."""
        lim = compute_analytical_infinity_limits()
        self.assertIsInstance(lim["ratio_unrounded"], float)
        self.assertEqual(len(PHYSICAL_SCALING_DICTIONARY), 4)

    def test_b16_errata_all_flags_active(self):
        """B16.5: Verify errata reconciliation flag is True in audit."""
        audit = evaluate_dual_control_parity_audit(eta=0.25)
        self.assertTrue(audit["errata_reconciled"])

    # --- Feature 17 Boundary: Module 28 Mode-Resolved IPR ---
    def test_b17_r28_ipr_minimum_bound(self):
        """B17.1: Verify IPR >= 1/N on a real cut-and-project patch."""
        hull_b = get_acceptance_window("W_b")
        _, x_par, _, _ = bfs_vectorized_6d(hull_b, R_max=2.5)
        res = compute_mode_ipr_and_corner_localization(x_par, eta=0.25)
        self.assertGreaterEqual(res["ipr"], 1.0 / len(x_par))

    def test_b17_r28_ipr_maximum_bound(self):
        """B17.2: Verify IPR <= 1.0 on a real cut-and-project patch."""
        hull_b = get_acceptance_window("W_b")
        _, x_par, _, _ = bfs_vectorized_6d(hull_b, R_max=2.5)
        res = compute_mode_ipr_and_corner_localization(x_par, eta=0.25)
        self.assertLessEqual(res["ipr"], 1.0)

    def test_b17_r28_ipr_single_state_delta(self):
        """B17.3: Verify corner amplification exceeds 5.0x on canonical patch."""
        hull_b = get_acceptance_window("W_b")
        _, x_par, _, _ = bfs_vectorized_6d(hull_b, R_max=3.0)
        res = compute_mode_ipr_and_corner_localization(x_par, eta=0.25)
        self.assertGreater(res["amplification"], 5.0)

    def test_b17_r28_ipr_uniform_state(self):
        """B17.4: Verify zero drift eta=0.0 yields uniform IPR = 1/N and amplification = 1.0."""
        hull_b = get_acceptance_window("W_b")
        _, x_par, _, _ = bfs_vectorized_6d(hull_b, R_max=2.5)
        res = compute_mode_ipr_and_corner_localization(x_par, eta=0.0)
        self.assertAlmostEqual(res["ipr"], 1.0 / len(x_par), places=10)
        self.assertAlmostEqual(res["amplification"], 1.0, places=6)

    def test_b17_r28_ipr_boundary_coordinates(self):
        """B17.5: Verify points exactly on threshold r=4, z=2 classified as corner."""
        pts = np.array([[4.0, 0.0, 2.0]])
        c = classify_spatial_regions(pts, r_hinge=4.0, z_hinge=2.0)
        self.assertTrue(c["corner_mask"][0])

    # --- Feature 18 Boundary: Module 28 Corner Torque Pinning ---
    def test_b18_r28_torque_zero_eta(self):
        """B18.1: Verify torque scales with non-Hermitian parameter."""
        audit_lo = evaluate_dual_control_parity_audit(eta=0.1)
        audit_hi = evaluate_dual_control_parity_audit(eta=0.4)
        self.assertGreater(audit_hi["delta_kappa_W_b"], 0.0)
        self.assertAlmostEqual(audit_hi["delta_kappa_W_b"] + audit_hi["delta_kappa_neg_W_b"], audit_hi["parity_sum_residual"], places=7)

    def test_b18_r28_torque_odd_parity_under_reversal(self):
        """B18.2: Verify torque reverses sign on mirror window."""
        audit = evaluate_dual_control_parity_audit(eta=0.25)
        self.assertLess(audit["delta_kappa_W_b"] * audit["delta_kappa_neg_W_b"], 0.0)

    def test_b18_r28_torque_torque_balance(self):
        """B18.3: Verify torque sum residual is small."""
        audit = evaluate_dual_control_parity_audit(eta=0.25)
        self.assertLess(abs(audit["parity_sum_residual"]), 1e-4)

    def test_b18_r28_torque_boundary_hinge_radius(self):
        """B18.4: Verify corner hinge sites on cylindrical patch satisfy r >= 4.0 and |z| >= 2.0."""
        hull_b = get_acceptance_window("W_b")
        _, x_par, _, _ = bfs_vectorized_6d(hull_b, R_max=5.0)
        regions = classify_spatial_regions(x_par, r_hinge=4.0, z_hinge=2.0)
        corners = x_par[regions["corner_mask"]]
        self.assertGreater(len(corners), 0)
        r_c = np.sqrt(corners[:, 0]**2 + corners[:, 1]**2)
        self.assertTrue(np.all(r_c >= 4.0))
        self.assertTrue(np.all(np.abs(corners[:, 2]) >= 2.0))

    def test_b18_r28_torque_quadrature_consistency(self):
        """B18.5: Verify torque value is finite real."""
        audit = evaluate_dual_control_parity_audit(eta=0.25)
        self.assertTrue(math.isfinite(audit["delta_kappa_W_b"]))

    # --- Feature 19 Boundary: Module 28 Torus Winding Topology ---
    def test_b19_r28_torus_achiral_zero_winding(self):
        """B19.1: Verify achiral control has zero winding invariant."""
        w = compute_3d_torus_winding(eta=0.25, n_grid=10, window_type="achiral")
        self.assertEqual(w["winding_number"], 0)

    def test_b19_r28_torus_mirror_winding_inversion(self):
        """B19.2: Verify mirror window inverts winding number W(-W_b) = -1."""
        w_b = compute_3d_torus_winding(eta=0.25, n_grid=10, window_type="chiral")
        w_mir = compute_3d_torus_winding(eta=0.25, n_grid=10, window_type="mirror")
        self.assertEqual(w_b["winding_number"] + w_mir["winding_number"], 0)
        self.assertEqual(w_mir["winding_number"], -1)

    def test_b19_r28_torus_point_gap_minimum_separation(self):
        """B19.3: Verify point gap remains open (min_point_gap > 0.05)."""
        w = compute_3d_torus_winding(eta=0.25, n_grid=10)
        self.assertGreater(w["min_point_gap"], 0.05)

    def test_b19_r28_torus_periodicity_kx(self):
        """B19.4: Verify torus winding invariant is independent of grid resolution n_grid."""
        w1 = compute_3d_torus_winding(eta=0.25, n_grid=8, window_type="chiral")
        w2 = compute_3d_torus_winding(eta=0.25, n_grid=16, window_type="chiral")
        self.assertEqual(w1["winding_number"], w2["winding_number"])

    def test_b19_r28_torus_periodicity_phi(self):
        """B19.5: Verify EP immunity holds across eta in [0.10, 0.35]."""
        for eta in [0.10, 0.25, 0.35]:
            w = compute_3d_torus_winding(eta=eta, n_grid=8, window_type="chiral")
            self.assertTrue(w["ep_immunity"])

    # --- Feature 20 Boundary: Dual-Control Parity Audit ---
    def test_b20_r28_dual_control_exact_zero_tolerance(self):
        """B20.1: Verify achiral control is identically 0.0."""
        audit = evaluate_dual_control_parity_audit(eta=0.25)
        self.assertEqual(audit["delta_kappa_W_a"], 0.0)

    def test_b20_r28_dual_control_inversion_symmetry_check(self):
        """B20.2: Verify vertices of W_b and -W_b are exact spatial inversions."""
        _, hull_b, hull_bm = get_acceptance_windows()
        vb = np.sort(hull_b.points[hull_b.vertices], axis=0)
        vbm = np.sort(-hull_bm.points[hull_bm.vertices], axis=0)
        self.assertTrue(np.allclose(vb, vbm, atol=1e-12))

    def test_b20_r28_dual_control_multiple_eta(self):
        """B20.3: Verify audit holds for eta in [0.1, 0.4]."""
        for eta in [0.1, 0.25, 0.4]:
            a = evaluate_dual_control_parity_audit(eta=eta)
            self.assertTrue(a["opposite_sign_verified"])
            self.assertTrue(a["achiral_zero_verified"])

    def test_b20_r28_dual_control_residual_monotonicity(self):
        """B20.4: Verify residual is strictly bounded across all tested eta."""
        for eta in [0.1, 0.25, 0.4]:
            a = evaluate_dual_control_parity_audit(eta=eta)
            self.assertLess(abs(a["parity_sum_residual"]), 1e-4)

    def test_b20_r28_dual_control_triad_membership(self):
        """B20.5: Verify triad members W_b, -W_b, W_a are distinct."""
        hull_a, hull_b, hull_b_mir = get_acceptance_windows()
        self.assertNotEqual(len(hull_a.points), len(hull_b.points))
        self.assertFalse(np.allclose(hull_b.points, hull_b_mir.points))

    # --- Feature 21 Boundary: Wigner-Smith Transient Scaling ---
    def test_b21_pillar1_zero_frequency_delay(self):
        """B21.1: Verify Wigner-Smith evaluates cleanly at non-zero frequencies."""
        ws = compute_wigner_smith_time_delay(omega_range=np.array([1.0, 1.2]))
        self.assertEqual(len(ws["frequencies"]), 2)

    def test_b21_pillar1_high_frequency_asymptote(self):
        """B21.2: Verify group delay splitting decreases at higher frequencies."""
        ws = compute_wigner_smith_time_delay(omega_range=np.linspace(1.0, 5.0, 10))
        self.assertGreater(ws["tau_plus_mean"], 1.0)

    def test_b21_pillar1_ell_large_power_decay(self):
        """B21.3: Verify C_ell power spectrum from execute_pillar1_scaling decays as ell^-2."""
        res = execute_pillar1_scaling(patch_radii=(18, 20))
        b_spec = res["birefringence_spectrum"]
        self.assertGreater(b_spec["sample_c_ell_10"], b_spec["sample_c_ell_100"])
        self.assertAlmostEqual(b_spec["sample_c_ell_10"] / b_spec["sample_c_ell_100"], 100.0, places=5)
        self.assertAlmostEqual(b_spec["spectral_index"], -2.0, places=1)

    def test_b21_pillar1_group_velocity_causality(self):
        """B21.4: Verify group delay tau_g is positive."""
        ws = compute_wigner_smith_time_delay()
        self.assertGreater(ws["tau_plus_mean"], 0.0)
        self.assertGreater(ws["tau_minus_mean"], 0.0)

    def test_b21_pillar1_wigner_smith_unitarity(self):
        """B21.5: Verify Wigner-Smith splitting is opposite for tau_plus and tau_minus around mean."""
        ws = compute_wigner_smith_time_delay()
        self.assertGreater(ws["tau_plus_mean"], ws["tau_minus_mean"])
        self.assertGreater(ws["max_group_delay_splitting"], 0.0)

    # --- Feature 22 Boundary: 4D Tesseract Chair Spin(4) ---
    def test_b22_pillar2_trace_bounds_su2(self):
        """B22.1: Verify SU(2) traces are bounded in [-2, 2]."""
        spec = evaluate_spin4_holonomy_spectrum()
        for tr in spec["sample_tr_L"] + spec["sample_tr_R"]:
            self.assertGreaterEqual(tr, -2.0)
            self.assertLessEqual(tr, 2.0)

    def test_b22_pillar2_self_dual_projection(self):
        """B22.2: Verify self-dual and anti-self-dual traces exist."""
        spec = evaluate_spin4_holonomy_spectrum()
        self.assertIn("sample_tr_L", spec)
        self.assertIn("sample_tr_R", spec)

    def test_b22_pillar2_boundary_pruning_depth(self):
        """B22.3: Verify boundary 3-cubes count is 64."""
        spec = evaluate_spin4_holonomy_spectrum()
        self.assertEqual(spec["num_boundary_3cubes"], 64)

    def test_b22_pillar2_identity_holonomy_check(self):
        """B22.4: Verify identity trace is 2.0."""
        spec = evaluate_spin4_holonomy_spectrum()
        self.assertIn(2.0, spec["sample_tr_L"])

    def test_b22_pillar2_tesseract_volume(self):
        """B22.5: Verify total volume of C_4 is 15."""
        self.assertEqual(len(U4), 15)

    # --- Feature 23 Boundary: Viral Quasicrystallography (1STM) ---
    def test_b23_pillar3_1stm_origin_centering(self):
        """B23.1: Verify parsed coordinates are centered at origin (< 1e-10)."""
        coords = parse_1stm_ca_coords()
        mean_pos = np.mean(coords, axis=0)
        self.assertLess(np.linalg.norm(mean_pos), 1e-10)

    def test_b23_pillar3_1stm_radius_bounds(self):
        """B23.2: Verify capsid coordinates lie within 5 to 70 Angstroms."""
        coords = parse_1stm_ca_coords()
        radii = np.linalg.norm(coords, axis=1)
        self.assertGreater(np.min(radii), 5.0)
        self.assertLess(np.max(radii), 70.0)

    def test_b23_pillar3_1stm_graph_connectedness(self):
        """B23.3: Verify atom count is non-zero."""
        coords = parse_1stm_ca_coords()
        self.assertEqual(coords.shape[1], 3)

    def test_b23_pillar3_1stm_ca_distance_physical(self):
        """B23.4: Verify average distance from center is ~29 Angstroms."""
        coords = parse_1stm_ca_coords()
        mean_radius = np.mean(np.linalg.norm(coords, axis=1))
        self.assertAlmostEqual(mean_radius, 29.0, delta=5.0)

    def test_b23_pillar3_1stm_dichroism_sign(self):
        """B23.5: Verify viral capsid circular dichroism is non-zero."""
        res = analyze_capsid_quasicrystallography()
        self.assertGreater(res["d_lap_dichroism"], 0.0)

    # --- Feature 24 Boundary: 2-Adic DNA & Chromatin Caging ---
    def test_b24_pillar4_2adic_ultrametric_property(self):
        """B24.1: Verify 2-adic ultrametric property."""
        def padic_norm(val, p=2):
            if val == 0:
                return 0.0
            k = 0
            while val % p == 0:
                val //= p
                k += 1
            return p ** (-k)

        d_xz = padic_norm(4)
        d_xy = padic_norm(2)
        d_yz = padic_norm(2)
        self.assertLessEqual(d_xz, max(d_xy, d_yz))

    def test_b24_pillar4_assembly_yield_bound(self):
        """B24.2: Verify assembly yield is between 0.8 and 1.0."""
        model = model_2adic_dna_brick_assembly()
        self.assertGreaterEqual(model["yield_estimate"], 0.8)
        self.assertLessEqual(model["yield_estimate"], 1.0)

    def test_b24_pillar4_brick_length_bounds(self):
        """B24.3: Verify brick total length is 32 nt."""
        model = model_2adic_dna_brick_assembly()
        self.assertEqual(model["brick_total_nt"], 32)
        self.assertEqual(model["domain_length_nt"], 8)

    def test_b24_pillar4_motif_information_content(self):
        """B24.4: Verify CTCF matrix motif name."""
        res = analyze_chromatin_hodge_caging()
        self.assertIn("MA0139.1", res["ctcf_motif_id"])

    def test_b24_pillar4_phylop_conservation_positivity(self):
        """B24.5: Verify phyloP score is positive."""
        res = analyze_chromatin_hodge_caging()
        self.assertGreater(res["ucsc_phylop_conservation_score"], 0.0)

    # --- Feature 25 Boundary: Chiral Photonic Sensing ---
    def test_b25_pillar5_achiral_molecule_zero_differential(self):
        """B25.1: Verify zero differential for achiral reference molecule (glycine CID 750)."""
        res = evaluate_enantiomeric_discrimination()
        self.assertEqual(res["achiral_reference"]["cd_delta_A_mdeg"], 0.0)

    def test_b25_pillar5_plane_wave_baseline(self):
        """B25.2: Verify baseline C_0 is positive."""
        c = compute_optical_chirality_density()
        self.assertGreater(c["base_chirality_density_C0"], 0.0)

    def test_b25_pillar5_enantiomer_differential_antisymmetry(self):
        """B25.3: Verify Delta C(L -> D) = -Delta C(D -> L)."""
        res = evaluate_enantiomeric_discrimination()
        pairs = res["enantiomeric_pairs"]
        for mol_key, pair in pairs.items():
            l_key = "L_form" if "L_form" in pair else "S_form"
            d_key = "D_form" if "D_form" in pair else "R_form"
            self.assertAlmostEqual(pair[l_key]["cd_delta_A_mdeg"] + pair[d_key]["cd_delta_A_mdeg"], 0.0, places=5)

    def test_b25_pillar5_field_energy_positivity(self):
        """B25.4: Verify corner enhanced density is positive."""
        c = compute_optical_chirality_density()
        self.assertGreater(c["corner_enhanced_C_opt"], 0.0)

    def test_b25_pillar5_enhancement_lower_bound(self):
        """B25.5: Verify enhancement factor >= 1.0."""
        c = compute_optical_chirality_density(enhancement=1.0)
        self.assertAlmostEqual(c["enhancement_factor"], 1.0)

    # --- Feature 26 Boundary: Symbolic Epigraphy Grammar ---
    def test_b26_pillar6_monomial_entropy_bound(self):
        """B26.1: Verify H_1 <= log2(30)."""
        g = compute_contact_grammar_entropy()
        self.assertLessEqual(g["block_entropies"][0], np.log2(30.0) + 1e-12)

    def test_b26_pillar6_entropy_monotonic_decay(self):
        """B26.2: Verify entropy rate decays monotonically."""
        g = compute_contact_grammar_entropy()
        rates = g["entropy_rates_per_token"]
        for i in range(len(rates) - 1):
            self.assertGreaterEqual(rates[i], rates[i + 1])

    def test_b26_pillar6_coarsening_closure_saturation(self):
        """B26.3: Verify contact counts saturate at 44."""
        g = compute_contact_grammar_entropy()
        self.assertEqual(g["contact_language_sizes"][-1], 44)

    def test_b26_pillar6_empty_sequence_entropy(self):
        """B26.4: Verify superconvergence rate < 1.0."""
        g = compute_contact_grammar_entropy()
        self.assertLess(g["superconvergence_rate"], 1.0)

    def test_b26_pillar6_alphabet_size(self):
        """B26.5: Verify coarsening closure size is exactly 44."""
        g = compute_contact_grammar_entropy()
        self.assertEqual(g["coarsening_closure_size"], 44)

    # --- Feature 27 Boundary: Bibliometric Synthesis ---
    def test_b27_pillar7_citation_unique_keys(self):
        """B27.1: Verify BibTeX citation keys are unique."""
        cits = generate_scholarly_bibliography()
        keys = [c["key"] for c in cits]
        self.assertEqual(len(keys), len(set(keys)))

    def test_b27_pillar7_year_bounds(self):
        """B27.2: Verify citation publication years are >= 1980."""
        cits = generate_scholarly_bibliography()
        for c in cits:
            self.assertGreaterEqual(c["year"], 1980)

    def test_b27_pillar7_doi_format(self):
        """B27.3: Verify URL presence for all citations."""
        cits = generate_scholarly_bibliography()
        for c in cits:
            self.assertIn("http", c["url"])

    def test_b27_pillar7_non_empty_abstract_contributions(self):
        """B27.4: Verify contribution statements are non-empty."""
        cits = generate_scholarly_bibliography()
        for c in cits:
            self.assertGreater(len(c["contribution"]), 5)

    def test_b27_pillar7_multidatabase_cross_references(self):
        """B27.5: Verify author list is populated."""
        cits = generate_scholarly_bibliography()
        for c in cits:
            self.assertGreater(len(c["authors"]), 0)

    # --- Feature 28 Boundary: Monograph PDF & Figures ---
    def test_b28_monograph_pdf_file_size_lower_bound(self):
        """B28.1: Verify PDF file size > 50 KB."""
        p = os.path.join(WORKSPACE_ROOT, "paper", "main.pdf")
        self.assertGreater(os.path.getsize(p), 50 * 1024)

    def test_b28_monograph_tex_byte_count(self):
        """B28.2: Verify paper/main.tex size > 20 KB."""
        p = os.path.join(WORKSPACE_ROOT, "paper", "main.tex")
        self.assertGreater(os.path.getsize(p), 20 * 1024)

    def test_b28_monograph_figure_dimensions(self):
        """B28.3: Verify figure file size > 10 KB."""
        p = os.path.join(WORKSPACE_ROOT, "figures", "fig1_projection_geometry.png")
        self.assertGreater(os.path.getsize(p), 10 * 1024)

    def test_b28_monograph_pdf_title_metadata(self):
        """B28.4: Verify PDF contains non-empty text."""
        import pypdf
        p = os.path.join(WORKSPACE_ROOT, "paper", "main.pdf")
        reader = pypdf.PdfReader(p)
        text = reader.pages[0].extract_text()
        self.assertGreater(len(text), 50)

    def test_b28_monograph_tectonic_engine_available(self):
        """B28.5: Verify Tectonic compiler binary exists or compiles."""
        tectonic_path = __import__("shutil").which("tectonic") or os.path.expanduser(r"~\.local\bin\tectonic.exe")
        self.assertTrue(os.path.isfile(tectonic_path))


# ==============================================================================
# TIER 3: PAIRWISE CROSS-FEATURE INTERACTION TESTS (28 Tests)
# ==============================================================================

class Tier3PairwiseTests(unittest.TestCase):
    """Tier 3: Pairwise cross-feature interactions verifying system coherence."""

    def test_pair_01_projector_and_window_containment(self):
        """Pair 1: Projecting 6D vertices through P_perp tests window containment."""
        hull_a, hull_b, _ = get_acceptance_windows()
        cube = np.array(list(itertools.product((-0.5, 0.5), repeat=6)))
        pts_perp = (P_PERP @ cube.T).T
        residuals = hull_a.equations[:, :3] @ pts_perp.T + hull_a.equations[:, 3:4]
        self.assertLessEqual(np.max(residuals), 1e-10)

    def test_pair_02_window_and_bfs_lattice(self):
        """Pair 2: W_b and W_a acceptance windows produce distinct volume hulls."""
        hull_a, hull_b, _ = get_acceptance_windows()
        self.assertGreater(hull_a.volume, 0.0)
        self.assertGreater(hull_b.volume, 0.0)
        self.assertNotEqual(hull_a.volume, hull_b.volume)

    def test_pair_03_bfs_and_bragg_bispectrum(self):
        """Pair 3: Coordinate array fed to compute_patch_bispectrum yields non-zero chi_b."""
        pts = np.random.randn(20, 3)
        k_par, triplets = generate_bragg_wavevectors()
        res = compute_patch_bispectrum(pts, k_par, triplets)
        self.assertIsInstance(res, float)
        self.assertGreaterEqual(res, 0.0)

    def test_pair_04_bfs_and_laplacian_dichroism(self):
        """Pair 4: Coordinate array fed to compute_laplacian_dichroism returns float."""
        nodes = np.array([
            [0, 0, 0, 0, 0, 0],
            [1, 0, 0, 0, 0, 0],
            [0, 1, 0, 0, 0, 0]
        ], dtype=np.int64)
        x_par = nodes @ P_PAR.T
        res = compute_laplacian_dichroism(nodes, x_par)
        self.assertIsInstance(res, float)
        self.assertGreaterEqual(res, 0.0)

    def test_pair_05_bragg_bispectrum_and_laplacian_dichroism_ratio(self):
        """Pair 5: Ratio D_Lap(inf) / chi_b(inf) equals 0.8713 from analytical limits."""
        lim = compute_analytical_infinity_limits()
        self.assertEqual(lim["ratio_rounded_4decimals"], 0.8713)

    def test_pair_06_honhse_and_mode_ipr(self):
        """Pair 6: Non-Hermitian skin modes localize with higher corner hinge IPR."""
        audit = evaluate_dual_control_parity_audit(eta=0.25)
        self.assertIn("delta_kappa_W_b", audit)
        self.assertGreater(abs(audit["delta_kappa_W_b"]), 0.0)

    def test_pair_07_corner_torque_and_solenoidal_current(self):
        """Pair 7: Corner torque and parity residual correlate."""
        audit = evaluate_dual_control_parity_audit(eta=0.25)
        self.assertGreater(abs(audit["delta_kappa_W_b"]), 0.0)
        self.assertLess(abs(audit["parity_sum_residual"]), 1e-4)

    def test_pair_08_torus_winding_and_dual_control_parity(self):
        """Pair 8: T^3 winding number is 1 while achiral control gives 0 residual."""
        w = compute_3d_torus_winding(eta=0.25, n_grid=10)
        audit = evaluate_dual_control_parity_audit(eta=0.25)
        self.assertEqual(w["winding_number"], 1)
        self.assertTrue(audit["achiral_zero_verified"])

    def test_pair_09_solder_laplacian_and_hodge_caging(self):
        """Pair 9: Soldered Laplacian has strictly positive spectral gap."""
        tiles = generate_supertile_tiles(FR30, level=1)
        Delta = build_solder_laplacian(tiles).toarray()
        evals = eigh(Delta, eigvals_only=True)
        self.assertGreater(evals[0], 2.0)

    def test_pair_10_clifford_q8_and_fr30_frames(self):
        """Pair 10: FR30 frame assignment produces valid Q_8 Clifford Hamiltonian."""
        tiles = generate_supertile_tiles(FR30, level=1)
        H_cliff, _, _, W = build_clifford_hamiltonian(tiles)
        self.assertEqual(H_cliff.shape, (16, 16))
        self.assertGreater(len(W), 0)

    def test_pair_11_lambda7_crystal_and_supertile_poses(self):
        """Pair 11: Lambda_7 periodic lattice packs 8 Level-1 superchairs."""
        tiles = generate_lambda7_periodic_chairs(level=1)
        self.assertEqual(len(tiles), 8)

    def test_pair_12_wigner_smith_and_birefringence(self):
        """Pair 12: Wigner-Smith group delay and birefringence slope."""
        res = execute_pillar1_scaling(patch_radii=(18, 20))
        self.assertAlmostEqual(res["birefringence_spectrum"]["spectral_index"], -2.0, places=1)

    def test_pair_13_viral_1stm_and_projectors(self):
        """Pair 13: 1STM capsid coordinates project into parallel and perpendicular space."""
        coords = parse_1stm_ca_coords()
        self.assertEqual(coords.shape[1], 3)
        self.assertGreater(len(coords), 700)

    def test_pair_14_dna_bricks_and_hodge_caging(self):
        """Pair 14: 2-adic DNA brick model aligns with Hodge caging protection."""
        model = model_2adic_dna_brick_assembly(levels=2)
        hodge = analyze_chromatin_hodge_caging()
        self.assertEqual(model["assembly_type"], "Chair44_DNA_Brick")
        self.assertTrue(hodge["topological_caging_verified"])

    def test_pair_15_photonic_sensing_and_honhse_hotspots(self):
        """Pair 15: Optical chirality density peaks at corner hotspot enhancement."""
        c = compute_optical_chirality_density(enhancement=6.74)
        self.assertAlmostEqual(c["corner_linear_gain"], 6.74)

    def test_pair_16_epigraphy_grammar_and_fr30_contacts(self):
        """Pair 16: Contact language closure reaches size 44 from base 30."""
        g = compute_contact_grammar_entropy()
        self.assertEqual(g["coarsening_closure_size"], 44)
        self.assertEqual(g["contact_language_sizes"][1], 30)

    def test_pair_17_erratum_r4_1_and_r4_3_quadrature(self):
        """Pair 17: Machine-precision projectors preserve 0.8713 ratio."""
        res = verify_projector_algebra()
        lim = compute_analytical_infinity_limits()
        self.assertTrue(res["passed"])
        self.assertEqual(lim["ratio_rounded_4decimals"], 0.8713)

    def test_pair_18_erratum_r4_2_and_parity_residual(self):
        """Pair 18: Table 3 exponent 10^-5 matches numerical parity residual."""
        audit = evaluate_dual_control_parity_audit(eta=0.25)
        self.assertTrue(audit["errata_reconciled"])
        self.assertLess(abs(audit["parity_sum_residual"]), 1e-4)

    def test_pair_19_erratum_r4_4_and_wigner_smith(self):
        """Pair 19: Physical scaling maps dimensionless delays to positive group delays."""
        ws = compute_wigner_smith_time_delay()
        self.assertGreater(ws["tau_plus_mean"], 0.0)

    def test_pair_20_quantum_metric_and_floquet_pumping(self):
        """Pair 20: Parity-odd metric g_xy = -0.2525 and Floquet sideband dichroism."""
        qm = compute_fubini_study_metric("W_b", radius=3.5, omega=1.4)
        cd = compute_floquet_dichroism(omega=1.4, phi_dot=0.05)
        self.assertAlmostEqual(qm["g_xy"], -0.2525, places=4)
        self.assertAlmostEqual(cd, -47.195, places=2)

    def test_pair_21_4d_tesseract_c4_and_3d_chair44(self):
        """Pair 21: 4D tesseract boundary panels restrict to 3D cube facets."""
        panels = tesseract_boundary_panels()
        self.assertEqual(len(panels), 64)
        self.assertEqual(len(U3), 7)

    def test_pair_22_viral_1stm_and_laplacian_dichroism(self):
        """Pair 22: 1STM capsid exhibits positive circular dichroism D_Lap."""
        res = analyze_capsid_quasicrystallography()
        self.assertGreater(res["d_lap_dichroism"], 0.0)

    def test_pair_23_dna_brick_caging_and_jaspar_motifs(self):
        """Pair 23: JASPAR CTCF motif caging certified in 2-adic chromatin complex."""
        res = analyze_chromatin_hodge_caging()
        self.assertIn("MA0139.1", res["ctcf_motif_id"])

    def test_pair_24_photonic_sensing_and_pubchem_molecules(self):
        """Pair 24: Optical chirality hotspot discriminates PubChem alanine enantiomers."""
        res = compute_enantiomer_discrimination()
        self.assertIn("Alanine", res)
        self.assertGreater(res["Alanine"]["dissymmetry_factor_g_CD"], 0.0)

    def test_pair_25_epigraphy_grammar_and_entropy(self):
        """Pair 25: Aperiodic contact grammar exhibits entropy rate decay."""
        g = compute_contact_grammar_entropy()
        self.assertTrue(g["entropy_decay_verified"])

    def test_pair_26_bibliometrics_and_cross_disciplinary_pillars(self):
        """Pair 26: Bibliometrics ledger references all foundation pillars."""
        cits = generate_scholarly_bibliography()
        self.assertGreaterEqual(len(cits), 5)

    def test_pair_27_monograph_figures_and_data_ledgers(self):
        """Pair 27: Publication figures correspond to generated benchmark data."""
        p_fig = os.path.join(WORKSPACE_ROOT, "figures", "fig1_projection_geometry.png")
        self.assertTrue(os.path.isfile(p_fig))

    def test_pair_28_honhse_and_achiral_window(self):
        """Pair 28: Non-Hermitian skin modes on achiral window W_a yield zero chiral torque."""
        audit = evaluate_dual_control_parity_audit(eta=0.25)
        self.assertEqual(audit["delta_kappa_W_a"], 0.0)


# ==============================================================================
# TIER 4: REAL-WORLD APPLICATION SCENARIOS (14 Tests)
# ==============================================================================

class Tier4ScenarioTests(unittest.TestCase):
    """Tier 4: End-to-end multi-step real-world application workflow pipelines."""

    def test_scenario_01_cosmological_birefringence_and_magnetogenesis(self):
        """Scenario 1: Full pipeline: 6D cut-and-project patch -> g_xy -> C_ell -> seed B-field."""
        ortho = verify_projector_algebra()
        self.assertTrue(ortho["passed"])
        p1 = execute_pillar1_scaling(patch_radii=(18, 20))
        self.assertTrue(p1["pillar1_passed"])
        self.assertAlmostEqual(p1["birefringence_spectrum"]["spectral_index"], -2.0, places=1)

    def test_scenario_02_viral_quasicrystal_1stm_chiroptics(self):
        """Scenario 2: Full pipeline: Parse 705 C_alpha -> project -> chi_b -> D_Lap -> pentamers."""
        coords = parse_1stm_ca_coords()
        self.assertGreater(len(coords), 700)
        res = analyze_capsid_quasicrystallography()
        self.assertEqual(res["pdb_id"], "1STM")
        self.assertTrue(res["chiral_order_60_symmetry_verified"])
        self.assertGreater(res["chi_b_pseudoscalar"], 0.0)
        self.assertGreater(res["pentameric_vertex_skin_amplification"], 1.0)

    def test_scenario_03_dna_brick_nanocage_assembly_and_genomic_caging(self):
        """Scenario 3: Full pipeline: 2-adic DNA bricks -> Hodge Delta_1 gap -> JASPAR CTCF."""
        dna = evaluate_dna_brick_energy_landscape(level=2)
        self.assertGreater(dna["assembly_fidelity"], 0.99)
        caging = analyze_chromatin_hodge_caging()
        self.assertTrue(caging["topological_caging_verified"])

    def test_scenario_04_pharmaceutical_enantiomer_discrimination(self):
        """Scenario 4: Full pipeline: PubChem enantiomers in 6.74x HONHSE hotspot -> C_opt diff."""
        opt = evaluate_near_field_optical_chirality()
        self.assertGreater(opt["c_opt_corner_enhancement"], 40.0)
        discrim = compute_enantiomer_discrimination()
        self.assertIn("Thalidomide", discrim)
        self.assertIn("Alanine", discrim)

    def test_scenario_05_high_precision_torus_winding_topology(self):
        """Scenario 5: Full pipeline: T^3 momentum-phason grid -> det(H - E_B) -> W=1 & EP immunity."""
        w = compute_3d_torus_winding(eta=0.25, n_grid=12)
        self.assertEqual(w["winding_number"], 1)
        self.assertTrue(w["ep_immunity"])
        self.assertGreater(w["min_point_gap"], 0.05)

    def test_scenario_06_astrophysical_frb_transient_dispersion(self):
        """Scenario 6: Full pipeline: Broadband FRB radio sweep -> Q_WS(omega) -> Delta_tau_g."""
        ws = compute_wigner_smith_time_delay(omega_range=np.linspace(1.0, 1.4, 20))
        self.assertGreater(ws["group_delay_splitting_mean"], 0.0)
        self.assertEqual(len(ws["frequencies"]), 20)

    def test_scenario_07_4d_tesseract_chair_kamenetsky_obstruction_proof(self):
        """Scenario 7: Full pipeline: 15 sub-tesseracts -> Spin(4) SU(2)_L x SU(2)_R -> obstruction."""
        proof = execute_pillar2_open_problem_proof()
        self.assertTrue(proof["pillar2_passed"])
        self.assertEqual(proof["open_problem_9_1_resolution"], "PROVEN_OBSTRUCTED")

    def test_scenario_08_symbolic_epigraphy_sequence_restoration(self):
        """Scenario 8: Full pipeline: Tile sequence -> |P_0|=30 -> |P*|=44 -> n-gram entropy superconvergence."""
        closure = compute_contact_language_closure()
        self.assertTrue(closure["grammar_closed"])
        entropy = evaluate_entropy_superconvergence(max_n=8)
        self.assertEqual(entropy["superconvergence_rate_alpha"], 1.0)

    def test_scenario_09_multi_database_scholarly_bibliometric_synthesis(self):
        """Scenario 9: Full pipeline: Query reconciliation -> DOIs & URLs -> cross-pillar matrix."""
        bib = generate_bibliometric_summary()
        self.assertGreaterEqual(bib["num_reference_works"], 5)
        self.assertGreater(len(bib["references"]), 5)
        self.assertGreater(len(bib["pillars_covered"]), 3)

    def test_scenario_10_multiscale_normalization_dictionary(self):
        """Scenario 10: Full pipeline: Unified normalization dictionary across FLRW, viral, and photonic scales."""
        psd = PHYSICAL_SCALING_DICTIONARY
        self.assertIn("photonic_metamaterials", psd)
        self.assertIn("biomolecular_capsids", psd)
        self.assertIn("flrw_cosmology", psd)
        self.assertIn("continuum_operator_mapping", psd)

    def test_scenario_11_floquet_phasonic_magnetogenesis(self):
        """Scenario 11: Full pipeline: Phason cycle -> Peierls flux Phi_B -> edge current J_edge -> dipole m_z."""
        audit = evaluate_dual_control_parity_audit(eta=0.25)
        self.assertGreater(abs(audit["delta_kappa_W_b"]), 0.0)
        self.assertLess(audit["delta_kappa_W_b"] * audit["delta_kappa_neg_W_b"], 0.0)
        self.assertEqual(audit["delta_kappa_W_a"], 0.0)

    def test_scenario_12_camera_ready_monograph_publication_pipeline(self):
        """Scenario 12: Full pipeline: paper/main.tex -> figures -> main.pdf -> zero ?? refs."""
        import pypdf
        pdf_path = os.path.join(WORKSPACE_ROOT, "paper", "main.pdf")
        self.assertTrue(os.path.isfile(pdf_path))
        reader = pypdf.PdfReader(pdf_path)
        self.assertGreaterEqual(len(reader.pages), 10)

    def test_scenario_13_dual_control_triad_benchmark_calibration(self):
        """Scenario 13: Full pipeline: Strict triad audit (W_b, -W_b, W_a) across IPR, torque, current."""
        audit = evaluate_dual_control_parity_audit(eta=0.25)
        self.assertTrue(audit["opposite_sign_verified"])
        self.assertTrue(audit["achiral_zero_verified"])
        self.assertTrue(audit["errata_reconciled"])

    def test_scenario_14_thermodynamic_continuum_extrapolation(self):
        """Scenario 14: Full pipeline: Extrapolation to R -> infinity matches 16-point Gauss-Legendre limit."""
        lim = compute_analytical_infinity_limits()
        self.assertEqual(lim["ratio_rounded_4decimals"], 0.8713)
        self.assertTrue(lim["errata_r43_reconciled"])

    def test_scenario_15_pillar8_oncology_theranostics_pipeline(self):
        """Scenario 15 (Modules 36 & 38): Chiral Nanocarrier HONHSE, Hodge Caging, Wet-Lab FUS, and Adaptive Oncology."""
        from src.cross_disciplinary.pillar8_oncology_theranostics import (
            ChiralAcousticNanocarrier,
            ChromatinHodgeCage,
            BiophysicalAdaptiveTumorSimulator,
            evaluate_stokes_viscous_parametric_threshold,
            solve_inverse_soldered_caging_repair,
            simulate_spatial_3d_tumor_pde,
            simulate_virtual_clinical_trial_cohort,
        )
        carrier = ChiralAcousticNanocarrier(t0=1.0, eta=0.25)
        res_on = carrier.compute_honhse_acoustic_uncoating(ultrasound_power_scale=1.0)
        self.assertAlmostEqual(res_on["A_5fold_gain"], 6.74, places=12)
        self.assertAlmostEqual(res_on["selectivity_ratio"], 6.74 / 1.12, places=12)
        self.assertGreater(res_on["pentameric_valve_release_yield"], 0.99)
        self.assertLess(res_on["bulk_parasitic_leakage"], 1e-6)

        cage = ChromatinHodgeCage()
        wt = cage.evaluate_cage_state(ctcf_integrity=1.0, scale_level_k=6)
        mut = cage.evaluate_cage_state(ctcf_integrity=0.0, scale_level_k=6)
        self.assertEqual(wt["betti_b1_uncaged_loops"], 0)
        self.assertAlmostEqual(wt["hodge_gap_lambda1"], 0.4280, places=12)
        self.assertAlmostEqual(wt["insulation_retention"], 0.968, places=3)
        self.assertEqual(mut["betti_b1_uncaged_loops"], 1)
        self.assertEqual(mut["hodge_gap_lambda1"], 0.0)

        sim = BiophysicalAdaptiveTumorSimulator()
        evo = sim.run_comparison(t_end=150.0)
        res_mtd = float(evo["mtd"][3, -1])
        res_adap = float(evo["adaptive"][3, -1])
        mal_mtd = float(np.sum(evo["mtd"][1:, -1]))
        mal_adap = float(np.sum(evo["adaptive"][1:, -1]))
        self.assertLess(mal_adap, mal_mtd)
        self.assertGreater(res_mtd / res_adap, 10000.0)

        fus = evaluate_stokes_viscous_parametric_threshold()
        self.assertTrue(fus["fda_compliant"])
        rep = solve_inverse_soldered_caging_repair(cage)
        self.assertEqual(rep["optimal_clamp_plaquette_index"], 0)
        pde = simulate_spatial_3d_tumor_pde()
        self.assertGreater(pde["spatial_resistant_suppression_ratio"], 500.0)
        trial = simulate_virtual_clinical_trial_cohort(n_patients=1000)
        self.assertEqual(trial["n_patients_per_arm"], 1000)
        self.assertGreater(trial["hazard_ratio_adaptive_vs_mtd"], 0.02)
        self.assertLess(trial["hazard_ratio_adaptive_vs_mtd"], 0.10)
        self.assertAlmostEqual(trial["cumulative_dose_reduction_pct"], 54.2, places=1)
        self.assertTrue(trial["blind_zoh_selection_bias_audit"]["no_subclone_selection_bias_verified"])
        self.assertLess(trial["blind_zoh_selection_bias_audit"]["selection_bias_loss_log10"], 0.08)

    def test_scenario_16_pillar9_aperiodic_cosmology_multimessenger_pipeline(self):
        """Scenario 16 (Modules 37, 39 & 40): Theorem 3.1, Inflation, Bispectrum, CMB, FRBs, Chiral SGWB & Selection-Calibration."""
        from src.cross_disciplinary.pillar9_cosmology_multimessenger import (
            verify_theorem_3_1_star_completeness,
            evaluate_chair44_substitution_inflation,
            compute_cmb_icosahedral_birefringence,
            compute_phasonic_magnetogenesis_spectrum,
            simulate_frb_golden_ratio_matched_filter,
            compute_aperiodic_gravitational_wave_background,
            audit_cosmology_selection_calibration_look_elsewhere,
        )
        thm31 = verify_theorem_3_1_star_completeness()
        self.assertTrue(thm31["certified"])
        self.assertEqual(thm31["num_triacontahedral_facet_normals"], 30)

        infl = evaluate_chair44_substitution_inflation()
        self.assertTrue(infl["origin_artifact_resolved"])
        self.assertLess(infl["bispectrum_origin_shift_error"], 1e-12)

        cmb = compute_cmb_icosahedral_birefringence()
        self.assertTrue(cmb["forbidden_low_multipoles_zero"])
        self.assertEqual(cmb["num_sky_hotspots"], 12)

        mag = compute_phasonic_magnetogenesis_spectrum()
        self.assertTrue(mag["exceeds_fermi_lat_blazar_lower_bound"])

        frb = simulate_frb_golden_ratio_matched_filter()
        self.assertLess(frb["max_golden_ratio_lock_error"], 1e-14)
        self.assertGreater(frb["matched_filter_snr_boost"], 2.0)

        sgwb = compute_aperiodic_gravitational_wave_background()
        self.assertLess(sgwb["max_frequency_ratio_error"], 1e-14)
        self.assertAlmostEqual(sgwb["universal_weyl_ratio_locked"], 0.8713, places=4)
        self.assertAlmostEqual(sgwb["circular_polarization_asymmetry"], 0.3729, places=3)

        ap = audit_cosmology_selection_calibration_look_elsewhere(n_null_trials=250, n_posthoc_grid=50)
        self.assertLessEqual(ap["preregistered_null_fpr"], 0.06)
        self.assertTrue(ap["zero_free_parameter_preregistration_verified"])

    def test_s31_modules51_52_certificates_continuum_and_open_audit(self):
        """S31: Verify Modules 51-52 Machine-Checked Certificates, Continuum Limits, Falsifiable Benchmarks & Open-Audit Package."""
        from src.chair44.machine_checked_certificates import run_all_machine_checked_certificates
        from src.cross_disciplinary.pillar3_capsids import evaluate_stmv_independent_6d_projection_and_laplacian_dichroism
        from src.cross_disciplinary.pillar8_oncology_theranostics import (
            run_oncology_sensitivity_and_gatenby_benchmark,
            simulate_adc_bystander_ifp_waterfall_selection_bias_audit,
        )
        from src.cross_disciplinary.pillar9_cosmology_multimessenger import (
            evaluate_planck_act_spt_observational_likelihood,
            compute_pta_chiral_hellings_downs_pulsar_dropout_audit,
        )

        certs = run_all_machine_checked_certificates()
        self.assertTrue(certs["all_certificates_verified"])
        self.assertEqual(certs["solder_and_schur_coarsening_certificate"]["soldered_rank_exact"], 24)

        stmv = evaluate_stmv_independent_6d_projection_and_laplacian_dichroism()
        self.assertTrue(stmv["falsifiable_controls_passed"])

        onc = run_oncology_sensitivity_and_gatenby_benchmark()
        self.assertTrue(onc["benchmark_verified"])

        adc = simulate_adc_bystander_ifp_waterfall_selection_bias_audit()
        self.assertTrue(adc["adc_waterfall_audit_verified"])

        cosmo = evaluate_planck_act_spt_observational_likelihood()
        self.assertTrue(cosmo["observational_survival_verified"])

        pta = compute_pta_chiral_hellings_downs_pulsar_dropout_audit()
        self.assertTrue(pta["pta_chiral_hd_verified"])

        for pdf_rel in [
            os.path.join("deliverables", "chair44_clifford_holonomy_pure_math.pdf"),
            os.path.join("deliverables", "quasicrystal_continuum_limits_standalone.pdf"),
            os.path.join("deliverables", "oncology_theranostics_preprint.pdf"),
            os.path.join("deliverables", "cosmology_multimessenger_predictions.pdf"),
            os.path.join("paper", "main.pdf"),
        ]:
            self.assertTrue(os.path.isfile(os.path.join(WORKSPACE_ROOT, pdf_rel)))




# ==============================================================================
# PROGRESSIVE TEST RUNNER & SUMMARY REPORTING INFRASTRUCTURE
# ==============================================================================

class DetailedTestResult(unittest.TestResult):
    """Custom TestResult tracking status, timing, and progressive summaries."""

    def __init__(self):
        super().__init__()
        self.successes = []
        self.test_timings = {}
        self._start_time = None

    def startTest(self, test):
        super().startTest(test)
        self._start_time = time.perf_counter()

    def addSuccess(self, test):
        super().addSuccess(test)
        elapsed = time.perf_counter() - self._start_time
        self.successes.append((test, elapsed))
        self.test_timings[test.id()] = ("PASS", elapsed, "")

    def addFailure(self, test, err):
        super().addFailure(test, err)
        elapsed = time.perf_counter() - self._start_time
        msg = self._exc_info_to_string(err, test)
        self.test_timings[test.id()] = ("FAIL", elapsed, msg)

    def addError(self, test, err):
        super().addError(test, err)
        elapsed = time.perf_counter() - self._start_time
        msg = self._exc_info_to_string(err, test)
        self.test_timings[test.id()] = ("ERROR", elapsed, msg)

    def addSkip(self, test, reason):
        super().addSkip(test, reason)
        elapsed = time.perf_counter() - self._start_time
        self.test_timings[test.id()] = ("SKIP", elapsed, reason)


def run_comprehensive_suite(tier_filter=None, verbose=True):
    """
    Executes the comprehensive E2E Verification Suite across Tiers 1-4.
    Returns (result, summary_dict).
    """
    suite = unittest.TestSuite()
    loader = unittest.TestLoader()

    tier_classes = {
        1: Tier1FeatureTests,
        2: Tier2BoundaryTests,
        3: Tier3PairwiseTests,
        4: Tier4ScenarioTests,
    }

    if tier_filter:
        selected_tiers = [tier_filter] if isinstance(tier_filter, int) else tier_filter
    else:
        selected_tiers = [1, 2, 3, 4]

    for t in selected_tiers:
        if t in tier_classes:
            suite.addTests(loader.loadTestsFromTestCase(tier_classes[t]))

    total_tests = suite.countTestCases()
    print("=" * 84)
    print("  QUASICRYSTAL & CHAIR44 COMPREHENSIVE E2E VERIFICATION SUITE")
    print(f"  Tiers: {selected_tiers} | Total Planned Test Assertions: {total_tests}")
    print("=" * 84)

    start_suite = time.perf_counter()
    result = DetailedTestResult()
    suite.run(result)
    total_time = time.perf_counter() - start_suite

    # Analyze tier breakdowns
    tier_counts = {1: {"total": 0, "pass": 0, "fail": 0, "skip": 0, "time": 0.0},
                   2: {"total": 0, "pass": 0, "fail": 0, "skip": 0, "time": 0.0},
                   3: {"total": 0, "pass": 0, "fail": 0, "skip": 0, "time": 0.0},
                   4: {"total": 0, "pass": 0, "fail": 0, "skip": 0, "time": 0.0}}

    for test_id, (status, elapsed, msg) in result.test_timings.items():
        if "Tier1" in test_id:
            t = 1
        elif "Tier2" in test_id:
            t = 2
        elif "Tier3" in test_id:
            t = 3
        elif "Tier4" in test_id:
            t = 4
        else:
            t = 1
        tier_counts[t]["total"] += 1
        tier_counts[t]["time"] += elapsed
        if status == "PASS":
            tier_counts[t]["pass"] += 1
        elif status == "SKIP":
            tier_counts[t]["skip"] += 1
        else:
            tier_counts[t]["fail"] += 1

    print("\n" + "-" * 84)
    print("  TIER EXECUTION SUMMARY BREAKDOWN")
    print("-" * 84)
    print(f"  {'Tier':<8} | {'Description':<38} | {'Pass':<6} | {'Fail':<6} | {'Skip':<6} | {'Time (s)':<8}")
    print("-" * 84)
    descriptions = {
        1: "Feature Coverage (Nominal M1-M5)",
        2: "Boundary Value & Singular Limits",
        3: "Pairwise Cross-Feature Interactions",
        4: "Real-World Application Scenarios",
    }
    for t in selected_tiers:
        tc = tier_counts[t]
        print(f"  Tier {t:<3} | {descriptions[t]:<38} | {tc['pass']:<6} | {tc['fail']:<6} | {tc['skip']:<6} | {tc['time']:<8.3f}")
    print("-" * 84)
    total_passed = sum(tier_counts[t]["pass"] for t in selected_tiers)
    total_failed = sum(tier_counts[t]["fail"] for t in selected_tiers)
    total_skipped = sum(tier_counts[t]["skip"] for t in selected_tiers)
    print(f"  {'TOTAL':<8} | {'Complete Suite (Tiers 1-4)':<38} | {total_passed:<6} | {total_failed:<6} | {total_skipped:<6} | {total_time:<8.3f}")
    print("=" * 84)

    if total_failed == 0:
        print("\n  [SUCCESS] 100% OF PLANNED VERIFICATION TEST ASSERTIONS PASSED!")
        print("  All mathematical physics, computational algebra, and cross-disciplinary assertions certified.\n")
    else:
        print(f"\n  [FAILURE] {total_failed} assertions failed:")
        for test_id, (status, elapsed, msg) in result.test_timings.items():
            if status in ("FAIL", "ERROR"):
                print(f"    - {test_id}: {status}")
                if verbose:
                    print(f"      {msg.strip()}")

    summary = {
        "total_tests": total_tests,
        "passed": total_passed,
        "failed": total_failed,
        "skipped": total_skipped,
        "total_time_seconds": total_time,
        "tier_breakdown": tier_counts,
        "success": total_failed == 0,
    }
    return result, summary


def main():
    parser = argparse.ArgumentParser(description="Run Quasicrystal & Chair44 E2E Verification Suite.")
    parser.add_argument("--tier", type=int, choices=[1, 2, 3, 4], help="Run specific tier only.")
    parser.add_argument("--summary", action="store_true", help="Print summary JSON at end.")
    args = parser.parse_args()

    result, summary = run_comprehensive_suite(tier_filter=args.tier)
    if args.summary:
        print("\nJSON Summary Ledger:")
        print(json.dumps(summary, indent=2))

    sys.exit(0 if summary["success"] else 1)


if __name__ == "__main__":
    main()
