"""
tests/test_chair44.py
================================================================================
Comprehensive Unit Test Suite for src/chair44:
  1. Chair Polytope Geometry, constituent cubes (N=7), panels (N=24), and facets.
  2. Kamenetsky FR30 Certified Contact Language (|P_0| = 30, |P^*| = 44, |F^*| = 135).
  3. Parameter-free Clifford Q_8 panel-normal connection, holonomies, and spectrum.
  4. Bimodal Soldered Laplacian & Level-1 Exact Algebraic Eigenvalues (< 1e-12).
  5. Polyhedral Cellular Cochain Complex (d1 d0 = 0, d2 d1 = 0) and Hodge Caging.
  6. Exact Pure-Translation Periodic Crystal on Lambda_7 = Ker(x + 2y + 4z mod 7).
================================================================================
"""

import os
import sys
import unittest
import numpy as np
from scipy.sparse import csr_matrix

sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), "..")))

from src.chair44.geometry import (
    U3, BASE_CENTERS, get_chair_cubes, get_chair_faces, perm_mat,
    generate_supertile_tiles, build_tile_adjacency
)
from src.chair44.frames import (
    FR30, ACHIRAL, CANONICAL_HOMO, compute_fr30_poses,
    get_valid_contact_pairs, verify_kamenetsky_theorems
)
from src.chair44.clifford import (
    SIGMA, q8_element_label, quaternion_trace, compute_clifford_holonomy,
    build_clifford_hamiltonian, analyze_clifford_q8_connection
)
from src.chair44.laplacians import (
    build_soldered_laplacian, analyze_soldered_laplacian,
    build_level1_tile_laplacian, compute_exact_level1_eigenvalues,
    compute_level1_tile_laplacian
)
from src.chair44.cellular_complex import (
    build_polyhedral_chair_complex, build_boundary_operators,
    compute_hodge_laplacians, verify_caging
)
from src.chair44.periodic_crystal import (
    homomorphic_map, get_lambda7_basis, generate_lambda7_periodic_chairs,
    generate_rotated_cell_periodic
)
from src.chair44.c4_tesseract import (
    compute_spin4_casimir_invariants,
    compute_c4_cell_complex_euler_characteristic,
    compute_c4_boundary_complex,
    compute_c4_cubical_homology_betti_numbers,
    compute_c4_hodge_laplacian_decomposition,
)


class TestChair44Suite(unittest.TestCase):

    def test_01_chair_cubes_and_faces(self):
        cubes = get_chair_cubes()
        self.assertEqual(len(cubes), 7, "C_3 must consist of exactly 7 unit cubes")
        self.assertNotIn((1, 1, 1), [tuple(c) for c in cubes], "(1,1,1) octant must be omitted")

        faces = get_chair_faces()
        self.assertEqual(len(faces), 24, "Boundary of C_3 must consist of exactly 24 unit square panels")
        
        outer_faces = [f for f in faces if f["facet_type"] == "outer"]
        inner_faces = [f for f in faces if f["facet_type"] == "inner"]
        self.assertEqual(len(outer_faces), 21, "C_3 must have 21 outer panels (4 on each of 3 full faces, 3 on each of 3 notched faces)")
        self.assertEqual(len(inner_faces), 3, "C_3 must have 3 inner socket panels (1 on each of 3 inner socket faces)")

    def test_02_fr30_hierarchical_contact_language(self):
        # Verify Level-2 and Level-3 contact language stabilization
        p0_lvl2 = compute_fr30_poses(2)
        self.assertEqual(len(p0_lvl2), 30, f"|P_0| at level 2 must equal 30, got {len(p0_lvl2)}")

        kam = verify_kamenetsky_theorems()
        self.assertTrue(kam["P0_certified_30"])
        self.assertEqual(kam["P0_count"], 30)
        self.assertEqual(kam["P_star_count"], 44)
        self.assertEqual(kam["facet_triples_F_star"], 135)
        self.assertTrue(kam["coarsening_closed"])

        pairs = get_valid_contact_pairs(1)
        self.assertGreater(len(pairs), 0)

    def test_03_clifford_q8_connection_and_holonomy(self):
        # 1. Pauli matrix algebra check
        self.assertTrue(np.allclose(SIGMA[0] @ SIGMA[1], 1j * SIGMA[2]))
        self.assertTrue(np.allclose(SIGMA[1] @ SIGMA[2], 1j * SIGMA[0]))
        self.assertTrue(np.allclose(SIGMA[2] @ SIGMA[0], 1j * SIGMA[1]))

        # 2. Q_8 element classification
        self.assertEqual(q8_element_label(np.eye(2)), "+1")
        self.assertEqual(q8_element_label(-np.eye(2)), "-1")
        self.assertEqual(q8_element_label(1j * SIGMA[0]), "+i")
        self.assertEqual(q8_element_label(-1j * SIGMA[0]), "-i")
        self.assertEqual(q8_element_label(1j * SIGMA[1]), "+j")
        self.assertEqual(q8_element_label(-1j * SIGMA[1]), "-j")
        self.assertEqual(q8_element_label(1j * SIGMA[2]), "+k")
        self.assertEqual(q8_element_label(-1j * SIGMA[2]), "-k")

        # 3. Connection and Holonomy on Level-1 superchair
        tiles_lvl1 = generate_supertile_tiles(FR30, 1)
        hol_counts, ev = analyze_clifford_q8_connection(tiles_lvl1)
        self.assertGreater(len(hol_counts), 0)
        self.assertEqual(len(ev), 16, "Level 1 Clifford Hamiltonian must have 2*N = 16 eigenvalues")
        
        # Verify non-trivial cycles exist
        nontriv = sum(v for k, v in hol_counts.items() if k != "+1")
        self.assertGreater(nontriv, 0, "Clifford connection must generate non-trivial Wilson loop holonomies")

    def test_04_soldered_laplacian_and_exact_algebraic_eigenvalues(self):
        # 1. Exact Level-1 algebraic eigenvalues
        comp_ev, exact_ev, max_err = compute_exact_level1_eigenvalues()
        self.assertLess(max_err, 1e-12, f"Level-1 algebraic eigenvalue error {max_err:.2e} >= 1e-12")
        self.assertAlmostEqual(comp_ev[0], 0.0, places=12)
        self.assertAlmostEqual(comp_ev[1], (21.0 - 3.0 * np.sqrt(5.0)) / 2.0, places=12)
        self.assertAlmostEqual(comp_ev[2], (21.0 - 3.0 * np.sqrt(5.0)) / 2.0, places=12)
        self.assertAlmostEqual(comp_ev[3], 15.0 - 3.0 * np.sqrt(2.0), places=12)
        self.assertAlmostEqual(comp_ev[4], (21.0 + 3.0 * np.sqrt(5.0)) / 2.0, places=12)
        self.assertAlmostEqual(comp_ev[5], (21.0 + 3.0 * np.sqrt(5.0)) / 2.0, places=12)
        self.assertAlmostEqual(comp_ev[6], 15.0 + 3.0 * np.sqrt(2.0), places=12)
        self.assertAlmostEqual(comp_ev[7], 24.0, places=12)

        # 2. Bimodal Soldered Laplacian Commutator Norm
        tiles = generate_supertile_tiles(FR30, 1)
        ev_solder, comm_norm = analyze_soldered_laplacian(tiles)
        self.assertEqual(len(ev_solder), 24, "3N = 24 eigenvalues for Level-1 soldered Laplacian")
        self.assertGreater(comm_norm, 100.0, f"Commutator norm ||[L_p, L_n]||_F = {comm_norm} <= 100.0")

    def test_05_polyhedral_cellular_complex_and_caging(self):
        tiles = generate_supertile_tiles(FR30, 1)
        d0, d1, d2, counts = build_polyhedral_chair_complex(tiles)
        
        # Boundary nilpotency d1 @ d0 = 0 and d2 @ d1 = 0
        diff10 = abs(d1 @ d0).sum()
        diff21 = abs(d2 @ d1).sum()
        self.assertEqual(diff10, 0, f"d1 @ d0 != 0 (sum = {diff10})")
        self.assertEqual(diff21, 0, f"d2 @ d1 != 0 (sum = {diff21})")

        # Hodge caging verification
        caging = verify_caging(d0, d1, d2)
        self.assertTrue(caging, "Polyhedral Hodge caging verification failed")

    def test_06_periodic_lambda7_crystal(self):
        # 1. Homomorphism test: phi maps U_3 bijectively to Z_7
        phi_vals = [homomorphic_map(u[0], u[1], u[2]) for u in U3]
        self.assertEqual(set(phi_vals), set(range(7)), "phi must map U_3 bijectively onto {0..6}")

        # 2. Determinant of Lambda_7 basis
        basis = get_lambda7_basis()
        det = int(round(np.linalg.det(basis)))
        self.assertEqual(det, 7, f"Lambda_7 basis determinant must equal 7, got {det}")

        # 3. Crystal tile generation
        tiles_p1 = generate_lambda7_periodic_chairs(1)
        self.assertEqual(len(tiles_p1), 8, "Level 1 periodic crystal must have 2^3 = 8 chairs")
        
        # Verify no overlapping cubes among the periodic chairs
        all_cubes = set()
        total_cube_count = 0
        for _, _, cubes in tiles_p1:
            all_cubes.update(cubes)
            total_cube_count += len(cubes)
        self.assertEqual(len(all_cubes), total_cube_count, "Periodic chairs must tile without overlaps")

    def test_07_spin4_casimir_invariants(self):
        cas = compute_spin4_casimir_invariants()
        self.assertTrue(cas["decoupling_verified"])
        self.assertAlmostEqual(cas["C_plus_norm"], -12.0)
        self.assertAlmostEqual(cas["C_minus_norm"], -12.0)
        self.assertLess(cas["err_casimir_plus"], 1e-14)
        self.assertLess(cas["err_casimir_minus"], 1e-14)
        self.assertLess(cas["max_cross_commutator"], 1e-14)

    def test_08_c4_cell_complex_euler_characteristic(self):
        """Pillar 2: Verify exact cell counts and contractibility chi(C_4) = 1."""
        cc = compute_c4_cell_complex_euler_characteristic()
        self.assertTrue(cc["contractible_verified"])
        self.assertEqual(cc["f0_vertices"], 80)
        self.assertEqual(cc["f1_edges"], 212)
        self.assertEqual(cc["f2_faces"], 210)
        self.assertEqual(cc["f3_cubes"], 92)
        self.assertEqual(cc["f4_tesseracts"], 15)
        self.assertEqual(cc["euler_characteristic_chi"], 1)

    def test_09_c4_boundary_complex_euler_characteristic(self):
        """Pillar 2: Verify exact boundary cell counts and closed 3-manifold chi(partial C_4) = 0."""
        bc = compute_c4_boundary_complex()
        self.assertTrue(bc["s3_topology_verified"])
        self.assertEqual(bc["f0_boundary_vertices"], 80)
        self.assertEqual(bc["f1_boundary_edges"], 208)
        self.assertEqual(bc["f2_boundary_faces"], 192)
        self.assertEqual(bc["f3_boundary_cubes"], 64)
        self.assertEqual(bc["boundary_euler_characteristic_chi"], 0)

    def test_10_c4_cubical_homology_betti_numbers(self):
        """Pillar 2: Verify exact cubical homology Betti numbers b(C_4) = (1,0,0,0,0) and b(del C_4) = (1,0,0,1)."""
        betti = compute_c4_cubical_homology_betti_numbers()
        self.assertTrue(betti["c4_contractible_homology_verified"])
        self.assertTrue(betti["boundary_s3_homology_verified"])
        self.assertEqual(betti["betti_c4"], [1, 0, 0, 0, 0])
        self.assertEqual(betti["betti_boundary_c4"], [1, 0, 0, 1])
        self.assertEqual(betti["ranks_c4"]["rank_d1"], 79)
        self.assertEqual(betti["ranks_c4"]["rank_d2"], 133)
        self.assertEqual(betti["ranks_c4"]["rank_d3"], 77)
        self.assertEqual(betti["ranks_c4"]["rank_d4"], 15)
        self.assertEqual(betti["ranks_boundary"]["rank_d1"], 79)
        self.assertEqual(betti["ranks_boundary"]["rank_d2"], 129)
        self.assertEqual(betti["ranks_boundary"]["rank_d3"], 63)

    def test_11_c4_hodge_laplacian_decomposition(self):
        """Pillar 2: Verify discrete Hodge Laplacian harmonic form dimensions dim ker Delta_k = b_k."""
        hodge = compute_c4_hodge_laplacian_decomposition()
        self.assertTrue(hodge["hodge_decomposition_verified"])
        self.assertEqual(hodge["dim_harmonic_k_forms_c4"], [1, 0, 0, 0, 0])
        self.assertEqual(hodge["dim_harmonic_k_forms_boundary"], [1, 0, 0, 1])
        self.assertEqual(hodge["laplacian_ranks_c4"], [79, 212, 210, 92, 15])
        self.assertEqual(hodge["laplacian_ranks_boundary"], [79, 208, 192, 63])


if __name__ == "__main__":
    unittest.main()

