"""
tests/test_adversarial_chair44.py
================================================================================
Empirical Challenger Adversarial Verification Test Suite for src/chair44.

Adversarial Stress Testing Across 5 Target Domains:
  1. Chair Polytope Geometry, Rep-2^N Disjoint Substitution & FR30 Contact Language.
  2. Clifford Q_8 Holonomy Cycles Under Arbitrary Spanning Tree Bases & Kramers Symmetry.
  3. Soldered Laplacian Commutator Norm, SO(3) Invariance & Level-1 Exact Spectrum.
  4. Polyhedral Cellular Complex Caging: Boundary Nilpotency, Homology & SUSY Trace Sum.
  5. Space-Filling Lambda_7 Periodic Crystal Gapless Packing, Det=7 Basis & Covering Oracle.
================================================================================
"""

import collections
import heapq
import itertools
import os
import random
import sys
import unittest

import numpy as np
from scipy.linalg import eigh
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


class TestAdversarialChairGeometry(unittest.TestCase):
    """Domain 1: Chair Geometry, Rep-2^N Substitution, and FR30 Contact Language."""

    def test_01_polytope_volume_and_socket(self):
        cubes = get_chair_cubes()
        self.assertEqual(len(cubes), 7, "C_3 must consist of exactly 7 constituent unit cubes")
        
        # Verify (1,1,1) is strictly omitted
        cube_tuples = set(tuple(c) for c in cubes)
        self.assertNotIn((1, 1, 1), cube_tuples, "Octant (1,1,1) must be strictly omitted from C_3")
        for c in cubes:
            self.assertTrue(all(coord in (0, 1) for coord in c), f"Cube origin {c} must be in {{0,1}}^3")

        # Monte Carlo volume verification
        rng = np.random.RandomState(42)
        n_samples = 100000
        pts = 2.0 * rng.rand(n_samples, 3)
        # Point in C_3 iff in [0,2]^3 and not in (1,2]^3
        in_chair = ~((pts[:, 0] > 1.0) & (pts[:, 1] > 1.0) & (pts[:, 2] > 1.0))
        mc_volume = 8.0 * np.mean(in_chair)
        self.assertAlmostEqual(mc_volume, 7.0, delta=0.03, msg="Monte Carlo volume must approximate 7.0")

    def test_02_panel_orientation_and_normals(self):
        faces = get_chair_faces()
        self.assertEqual(len(faces), 24, "Boundary of C_3 must consist of exactly 24 unit square panels")

        outer_faces = [f for f in faces if f["facet_type"] == "outer"]
        inner_faces = [f for f in faces if f["facet_type"] == "inner"]
        self.assertEqual(len(outer_faces), 21, "C_3 must have exactly 21 outer panels")
        self.assertEqual(len(inner_faces), 3, "C_3 must have exactly 3 inner socket panels")

        # Verify outward-pointing unit normals
        for f in faces:
            norm = f["normal"]
            ax = f["axis"]
            self.assertIn(norm[ax], (-1, 1), "Panel normal along axis must be +-1")
            self.assertEqual(sum(abs(x) for x in norm), 1, "Panel normal must be a unit coordinate vector")

    def test_03_rep2n_substitution_gapless_and_overlap_free(self):
        for k in (1, 2, 3):
            tiles = generate_supertile_tiles(FR30, k)
            expected_tile_count = 8 ** k
            expected_cube_count = 7 * expected_tile_count
            self.assertEqual(len(tiles), expected_tile_count, f"Level {k} must have {expected_tile_count} tiles")

            all_cubes = [c for _, _, cs in tiles for c in cs]
            unique_cubes = set(all_cubes)
            self.assertEqual(len(all_cubes), expected_cube_count, f"Level {k} must contain {expected_cube_count} cubes")
            self.assertEqual(
                len(unique_cubes), expected_cube_count,
                f"Level {k} tiles must have zero overlaps (disjoint cube partition)"
            )

            # Check bounding box containment: all cubes in [0, 2^{k+1}]^3 \ (2^k, 2^{k+1}]^3
            scale = 2 ** k
            for cx, cy, cz in unique_cubes:
                self.assertTrue(0 <= cx < 2 * scale and 0 <= cy < 2 * scale and 0 <= cz < 2 * scale)
                self.assertFalse(
                    cx >= scale and cy >= scale and cz >= scale,
                    f"Cube ({cx},{cy},{cz}) must not invade the missing socket (scale={scale})"
                )

    def test_04_strict_homochirality(self):
        for k in (1, 2, 3):
            tiles = generate_supertile_tiles(FR30, k)
            for a, (G, _, _) in enumerate(tiles):
                det = int(round(np.linalg.det(G)))
                self.assertEqual(det, 1, f"Tile {a} at level {k} must have det(G) = +1 (homochiral SO(3))")
                # Orthogonality check
                self.assertTrue(np.allclose(G @ G.T, np.eye(3)), f"Tile {a} orientation G must be orthogonal")

    def test_05_fr30_contact_language_stabilization(self):
        p0_lvl1 = compute_fr30_poses(1)
        p0_lvl2 = compute_fr30_poses(2)
        p0_lvl3 = compute_fr30_poses(3)

        self.assertEqual(len(p0_lvl1), 21, f"Level 1 relative poses must equal 21, got {len(p0_lvl1)}")
        self.assertEqual(len(p0_lvl2), 30, f"Level 2 relative poses must equal 30, got {len(p0_lvl2)}")
        self.assertEqual(len(p0_lvl3), 30, f"Level 3 relative poses must stabilize to 30, got {len(p0_lvl3)}")
        self.assertEqual(p0_lvl2, p0_lvl3, "Contact language P_0 must be strictly identical between levels 2 and 3")

        # Pose inversion symmetry: (R, t) in P0 <=> (R^T, -R^T t) in P0
        for R_tup, t_tup in p0_lvl3:
            R = np.array(R_tup)
            t = np.array(t_tup)
            inv_R = tuple(map(tuple, R.T))
            inv_t = tuple(-R.T @ t)
            self.assertIn((inv_R, inv_t), p0_lvl3, "Relative pose set P_0 must be closed under inversion")

    def test_06_achiral_and_canonical_controls_pose_contrast(self):
        def get_poses(fdict, k):
            tiles = generate_supertile_tiles(fdict, k)
            owner = {c: a for a, (_, _, cubes) in enumerate(tiles) for c in cubes}
            poses = set()
            for (x, y, z), a in owner.items():
                for dx, dy, dz in [(1, 0, 0), (0, 1, 0), (0, 0, 1)]:
                    b = owner.get((x + dx, y + dy, z + dz))
                    if b is not None and b != a:
                        for u, v in [(a, b), (b, a)]:
                            Gu, Tu, _ = tiles[u]
                            Gv, Tv, _ = tiles[v]
                            poses.add((tuple(map(tuple, Gu.T @ Gv)), tuple(Gu.T @ (Tv - Tu))))
            return poses

        achiral_p0 = get_poses(ACHIRAL, 3)
        canon_p0 = get_poses(CANONICAL_HOMO, 3)
        self.assertEqual(len(achiral_p0), 26, "ACHIRAL control stabilizes at 26 poses")
        self.assertEqual(len(canon_p0), 26, "CANONICAL_HOMO control stabilizes at 26 poses")
        self.assertNotEqual(len(achiral_p0), 30, "Control languages must strictly differ from FR30")


class TestAdversarialCliffordHolonomy(unittest.TestCase):
    """Domain 2: Clifford Q_8 Holonomy Cycles Under Arbitrary Spanning Tree Bases & Kramers Symmetry."""

    def test_01_pauli_and_q8_group_closure(self):
        # Check standard Pauli algebra
        for i in range(3):
            self.assertTrue(np.allclose(SIGMA[i] @ SIGMA[i], np.eye(2)))
        self.assertTrue(np.allclose(SIGMA[0] @ SIGMA[1], 1j * SIGMA[2]))
        self.assertTrue(np.allclose(SIGMA[1] @ SIGMA[2], 1j * SIGMA[0]))
        self.assertTrue(np.allclose(SIGMA[2] @ SIGMA[0], 1j * SIGMA[1]))

        # Check closure of Q_8
        q8_elements = [
            np.eye(2, dtype=complex), -np.eye(2, dtype=complex),
            1j * SIGMA[0], -1j * SIGMA[0],
            1j * SIGMA[1], -1j * SIGMA[1],
            1j * SIGMA[2], -1j * SIGMA[2],
        ]
        for g1 in q8_elements:
            for g2 in q8_elements:
                prod = g1 @ g2
                self.assertNotEqual(q8_element_label(prod), "other", "Q_8 must be closed under multiplication")

    def test_02_arbitrary_spanning_trees_monte_carlo(self):
        tiles = generate_supertile_tiles(FR30, 1)
        n = len(tiles)
        H_cliff, panel_edges = build_clifford_hamiltonian(tiles)

        adj = collections.defaultdict(list)
        for idx, (u, v, Cab) in enumerate(panel_edges):
            adj[u].append((v, Cab, idx))
            adj[v].append((u, Cab.conj().T, idx))

        rng = random.Random(1337)
        non_trivial_fractions = []

        # Run 100 randomized spanning tree tests with random edge weights and random roots
        for trial in range(100):
            edge_weights = {idx: rng.random() for idx in range(len(panel_edges))}
            root = rng.randint(0, n - 1)
            visited = {root}
            tree_edges = set()
            T_root = {root: np.eye(2, dtype=complex)}

            # Randomized Prim algorithm
            pq = []
            for v, Cab, idx in adj[root]:
                heapq.heappush(pq, (edge_weights[idx], root, v, Cab, idx))

            while pq and len(visited) < n:
                w, u, v, Cab, idx = heapq.heappop(pq)
                if v in visited:
                    continue
                visited.add(v)
                tree_edges.add(idx)
                T_root[v] = T_root[u] @ Cab
                for nxt, C_nxt, nxt_idx in adj[v]:
                    if nxt not in visited:
                        heapq.heappush(pq, (edge_weights[nxt_idx], v, nxt, C_nxt, nxt_idx))

            self.assertEqual(len(visited), n, "Spanning tree must span all vertices")
            self.assertEqual(len(tree_edges), n - 1, f"Spanning tree must have exactly {n-1} edges")

            # Check fundamental cycle holonomies
            hol_counts = collections.Counter()
            for idx, (u, v, Cab) in enumerate(panel_edges):
                if idx in tree_edges:
                    continue
                H_loop = T_root[u] @ Cab @ T_root[v].conj().T
                lbl = q8_element_label(H_loop)
                self.assertNotEqual(lbl, "other", f"Trial {trial}: loop holonomy must be strictly in Q_8")
                hol_counts[lbl] += 1

            n_cycles = sum(hol_counts.values())
            self.assertEqual(n_cycles, len(panel_edges) - (n - 1), "Fundamental cycle count = |E| - (|V| - 1)")
            n_nontriv = sum(v for k_lbl, v in hol_counts.items() if k_lbl != "+1")
            frac = n_nontriv / n_cycles
            non_trivial_fractions.append(frac)
            self.assertGreater(n_nontriv, 0, f"Trial {trial}: spanning tree must yield non-trivial holonomies")

        # Ensure average non-trivial fraction exceeds 40% across all 100 spanning tree bases
        mean_nontriv = np.mean(non_trivial_fractions)
        min_nontriv = min(non_trivial_fractions)
        self.assertGreaterEqual(min_nontriv, 0.40, f"Minimum non-trivial cycle fraction {min_nontriv:.3f} must be >= 0.40")
        self.assertGreaterEqual(mean_nontriv, 0.55, f"Mean non-trivial cycle fraction {mean_nontriv:.3f} must be >= 0.55")

    def test_03_level2_spanning_trees(self):
        tiles2 = generate_supertile_tiles(FR30, 2)
        n = len(tiles2)
        H_cliff2, panel_edges2 = build_clifford_hamiltonian(tiles2)
        self.assertEqual(n, 64)
        self.assertEqual(len(panel_edges2), 576)

        adj = collections.defaultdict(list)
        for idx, (u, v, Cab) in enumerate(panel_edges2):
            adj[u].append((v, Cab, idx))
            adj[v].append((u, Cab.conj().T, idx))

        rng = random.Random(777)
        for trial in range(5):
            edge_weights = {idx: rng.random() for idx in range(len(panel_edges2))}
            root = rng.randint(0, n - 1)
            visited = {root}
            tree_edges = set()
            T_root = {root: np.eye(2, dtype=complex)}

            pq = []
            for v, Cab, idx in adj[root]:
                heapq.heappush(pq, (edge_weights[idx], root, v, Cab, idx))

            while pq and len(visited) < n:
                w, u, v, Cab, idx = heapq.heappop(pq)
                if v in visited:
                    continue
                visited.add(v)
                tree_edges.add(idx)
                T_root[v] = T_root[u] @ Cab
                for nxt, C_nxt, nxt_idx in adj[v]:
                    if nxt not in visited:
                        heapq.heappush(pq, (edge_weights[nxt_idx], v, nxt, C_nxt, nxt_idx))

            hol_counts = collections.Counter()
            for idx, (u, v, Cab) in enumerate(panel_edges2):
                if idx in tree_edges:
                    continue
                H_loop = T_root[u] @ Cab @ T_root[v].conj().T
                lbl = q8_element_label(H_loop)
                self.assertNotEqual(lbl, "other")
                hol_counts[lbl] += 1

            n_cycles = sum(hol_counts.values())
            self.assertEqual(n_cycles, 576 - 63)
            n_nontriv = sum(v for k, v in hol_counts.items() if k != "+1")
            self.assertGreaterEqual(n_nontriv / n_cycles, 0.60)

    def test_04_clifford_hamiltonian_hermiticity_and_kramers_degeneracy(self):
        tiles = generate_supertile_tiles(FR30, 1)
        H_cliff, _ = build_clifford_hamiltonian(tiles)

        # Hermiticity
        herm_err = np.max(np.abs(H_cliff - H_cliff.conj().T))
        self.assertLess(herm_err, 1e-15, f"H_cliff must be strictly Hermitian, got error {herm_err:.2e}")

        # Eigenvalues
        ev = np.sort(np.real(eigh(H_cliff, eigvals_only=True)))
        self.assertEqual(len(ev), 16, "Level 1 Clifford Hamiltonian must have 2N = 16 eigenvalues")

        # Positive semi-definiteness & positive spectral gap
        self.assertGreater(ev[0], 2.5, f"Clifford Hamiltonian ground state {ev[0]} must have a positive gap")

        # Kramers Time-Reversal Degeneracy: all eigenvalues must appear in degenerate pairs
        for i in range(0, 16, 2):
            diff = abs(ev[i] - ev[i + 1])
            self.assertLess(diff, 1e-13, f"Kramers pair ({i},{i+1}) degeneracy error {diff:.2e} >= 1e-13")


class TestAdversarialSolderedLaplacian(unittest.TestCase):
    """Domain 3: Soldered Laplacian Commutator Norm, SO(3) Invariance & Exact Algebraic Spectrum."""

    def test_01_soldered_laplacian_symmetry_and_trace(self):
        tiles1 = generate_supertile_tiles(FR30, 1)
        Ls, Lp, Ln = build_soldered_laplacian(tiles1)

        # Symmetry
        self.assertLess(np.max(np.abs(Lp - Lp.T)), 1e-15, "L_proto must be symmetric")
        self.assertLess(np.max(np.abs(Ln - Ln.T)), 1e-15, "L_normal must be symmetric")
        self.assertLess(np.max(np.abs(Ls - Ls.T)), 1e-15, "L_solder must be symmetric")

        # Commutator properties
        comm = Lp @ Ln - Ln @ Lp
        # Anti-symmetry: [A, B]^T = -[A, B] for symmetric A, B
        anti_sym_err = np.max(np.abs(comm + comm.T))
        self.assertLess(anti_sym_err, 1e-14, "Commutator of symmetric matrices must be strictly skew-symmetric")
        self.assertLess(abs(np.trace(comm)), 1e-14, "Trace of commutator must be strictly zero")

    def test_02_commutator_norm_exactness_and_so3_invariance(self):
        tiles1 = generate_supertile_tiles(FR30, 1)
        _, Lp, Ln = build_soldered_laplacian(tiles1)
        comm_norm_orig = float(np.linalg.norm(Lp @ Ln - Ln @ Lp))

        self.assertAlmostEqual(comm_norm_orig, 130.35336589, places=6, msg="Level 1 commutator norm mismatch")

        # Generate all 24 proper rotations in the cubic group O_h \cap SO(3)
        rots = []
        for p in [(0, 1, 2), (0, 2, 1), (1, 0, 2), (1, 2, 0), (2, 0, 1), (2, 1, 0)]:
            for s0 in (1, -1):
                for s1 in (1, -1):
                    for s2 in (1, -1):
                        R = np.zeros((3, 3), dtype=int)
                        R[0, p[0]] = s0
                        R[1, p[1]] = s1
                        R[2, p[2]] = s2
                        if int(round(np.linalg.det(R))) == 1:
                            rots.append(R)

        self.assertEqual(len(rots), 24, "Cubic rotational group has exactly 24 elements")

        # Test invariance of commutator norm under all 24 global rotations
        for R in rots:
            rot_tiles = []
            for G, T, cubes in tiles1:
                new_G = R @ G
                new_T = R @ T
                new_cubes = {tuple(R @ np.array(c)) for c in cubes}
                rot_tiles.append((new_G, new_T, new_cubes))
            _, Lp_r, Ln_r = build_soldered_laplacian(rot_tiles)
            norm_r = float(np.linalg.norm(Lp_r @ Ln_r - Ln_r @ Lp_r))
            self.assertAlmostEqual(norm_r, comm_norm_orig, places=8, msg="Commutator norm must be strictly SO(3) invariant")

    def test_03_level1_tile_laplacian_characteristic_polynomial(self):
        L = build_level1_tile_laplacian()
        self.assertEqual(L.shape, (8, 8))
        self.assertEqual(np.trace(L), 96.0, "Trace of Level-1 Tile Laplacian must equal 96")

        # Symbolic characteristic polynomial expansion:
        # P(lambda) = lambda * (lambda - 24) * (lambda^2 - 30*lambda + 207) * (lambda^2 - 21*lambda + 99)^2
        # Exact integer coefficients:
        expected_coeffs = [1, -96, 3834, -82566, 1035342, -7558272, 29742471, -48691368, 0]

        # Compute numerical characteristic polynomial via Faddeev-LeVerrier algorithm in integer arithmetic
        A = L.astype(int)
        n = 8
        c = [1]
        M = np.zeros((n, n), dtype=object)
        for k in range(1, n + 1):
            if k == 1:
                M = A.copy()
            else:
                M = A @ (M + c[-1] * np.eye(n, dtype=object))
            tr = np.trace(M)
            c.append(int(-tr // k))

        self.assertEqual(c, expected_coeffs, "Level-1 Tile Laplacian charpoly must match exact integer formula identically")

    def test_04_level1_tile_laplacian_algebraic_roots_exactness(self):
        computed_evals, exact_evals, max_err = compute_exact_level1_eigenvalues()
        self.assertLess(max_err, 1.1e-14, f"Level-1 algebraic eigenvalue error {max_err:.2e} >= 1.1e-14")
        self.assertLess(max_err, 1e-12, "Error must be well below 1e-12 threshold")

    def test_05_laplacian_perturbation_lipschitz_stability(self):
        L = build_level1_tile_laplacian()
        ev0 = np.sort(eigh(L, eigvals_only=True))
        rng = np.random.RandomState(42)

        for eps in (1e-8, 1e-6, 1e-4):
            E = rng.randn(8, 8)
            E = 0.5 * (E + E.T)
            norm_E = np.linalg.norm(E, 2)
            L_pert = L + eps * E
            ev_pert = np.sort(eigh(L_pert, eigvals_only=True))
            max_shift = np.max(np.abs(ev_pert - ev0))
            self.assertLessEqual(max_shift, eps * norm_E + 1e-14, "Weyl eigenvalue perturbation bound violated")


class TestAdversarialPolyhedralComplexAndCaging(unittest.TestCase):
    """Domain 4: Polyhedral Complex Boundary Nilpotency, Homology & Supersymmetry Trace Sum."""

    def test_01_boundary_nilpotency_level1_and_level2(self):
        # Level 1
        tiles1 = generate_supertile_tiles(FR30, 1)
        d0_1, d1_1, d2_1, counts_1 = build_polyhedral_chair_complex(tiles1)
        self.assertEqual(counts_1, (117, 252, 144, 8))
        self.assertEqual(abs(d1_1 @ d0_1).sum(), 0.0, "Level 1 d1 @ d0 must be strictly 0")
        self.assertEqual(abs(d2_1 @ d1_1).sum(), 0.0, "Level 1 d2 @ d1 must be strictly 0")

        # Level 2
        tiles2 = generate_supertile_tiles(FR30, 2)
        d0_2, d1_2, d2_2, counts_2 = build_polyhedral_chair_complex(tiles2)
        self.assertEqual(counts_2, (665, 1560, 960, 64))
        self.assertEqual(abs(d1_2 @ d0_2).sum(), 0.0, "Level 2 d1 @ d0 must be strictly 0")
        self.assertEqual(abs(d2_2 @ d1_2).sum(), 0.0, "Level 2 d2 @ d1 must be strictly 0")

    def test_02_euler_characteristic_and_contractibility(self):
        tiles1 = generate_supertile_tiles(FR30, 1)
        d0, d1, d2, (nV, nE, nF, nT) = build_polyhedral_chair_complex(tiles1)

        chi = nV - nE + nF - nT
        self.assertEqual(chi, 1, "Level 1 complex must have Euler characteristic chi = 1")

        r0 = np.linalg.matrix_rank(d0.toarray())
        r1 = np.linalg.matrix_rank(d1.toarray())
        r2 = np.linalg.matrix_rank(d2.toarray())
        self.assertEqual(r0, 116)
        self.assertEqual(r1, 136)
        self.assertEqual(r2, 8)

        b0 = nV - r0
        b1 = (nE - r0) - r1
        b2 = (nF - r1) - r2
        b3 = nT - r2
        self.assertEqual((b0, b1, b2, b3), (1, 0, 0, 0), "Superchair complex must have Betti numbers (1,0,0,0)")

    def test_03_supersymmetry_trace_cancellation_generalized(self):
        tiles1 = generate_supertile_tiles(FR30, 1)
        d0, d1, d2, _ = build_polyhedral_chair_complex(tiles1)
        D0, D1, D2, D3 = compute_hodge_laplacians(d0, d1, d2)

        evs = [np.sort(eigh(D.toarray(), eigvals_only=True)) for D in (D0, D1, D2, D3)]
        tol = 1e-8

        # Test 5 distinct spectral test functions f(lambda)
        test_functions = [
            ("sqrt", lambda x: np.sqrt(x)),
            ("linear", lambda x: x),
            ("quadratic", lambda x: x ** 2),
            ("heat_kernel", lambda x: np.exp(-0.5 * x)),
            ("log_resolvent", lambda x: np.log1p(x)),
        ]

        for name, f in test_functions:
            s0 = np.sum(f(evs[0][evs[0] > tol]))
            s1 = np.sum(f(evs[1][evs[1] > tol]))
            s2 = np.sum(f(evs[2][evs[2] > tol]))
            s3 = np.sum(f(evs[3][evs[3] > tol]))
            susy_sum = s0 - s1 + s2 - s3
            self.assertLess(abs(susy_sum), 1e-12, f"SUSY cancellation for {name} failed: sum = {susy_sum:.2e}")

    def test_04_metric_perturbation_invariance(self):
        tiles1 = generate_supertile_tiles(FR30, 1)
        d0, d1, d2, (nV, nE, nF, nT) = build_polyhedral_chair_complex(tiles1)

        rng = np.random.RandomState(42)
        w0 = np.exp(0.5 * rng.randn(nV))
        w1 = np.exp(0.5 * rng.randn(nE))
        w2 = np.exp(0.5 * rng.randn(nF))
        w3 = np.exp(0.5 * rng.randn(nT))

        d0_pert = np.diag(np.sqrt(w1)) @ d0.toarray() @ np.diag(1.0 / np.sqrt(w0))
        d1_pert = np.diag(np.sqrt(w2)) @ d1.toarray() @ np.diag(1.0 / np.sqrt(w1))
        d2_pert = np.diag(np.sqrt(w3)) @ d2.toarray() @ np.diag(1.0 / np.sqrt(w2))

        # Boundary nilpotency must strictly hold
        self.assertLess(np.max(np.abs(d1_pert @ d0_pert)), 1e-14)
        self.assertLess(np.max(np.abs(d2_pert @ d1_pert)), 1e-14)

        D0_p = d0_pert.T @ d0_pert
        D1_p = d0_pert @ d0_pert.T + d1_pert.T @ d1_pert
        D2_p = d1_pert @ d1_pert.T + d2_pert.T @ d2_pert
        D3_p = d2_pert @ d2_pert.T

        evs_p = [np.sort(eigh(D, eigvals_only=True)) for D in (D0_p, D1_p, D2_p, D3_p)]
        tol = 1e-7
        s0_p = np.sum(np.sqrt(evs_p[0][evs_p[0] > tol]))
        s1_p = np.sum(np.sqrt(evs_p[1][evs_p[1] > tol]))
        s2_p = np.sum(np.sqrt(evs_p[2][evs_p[2] > tol]))
        s3_p = np.sum(np.sqrt(evs_p[3][evs_p[3] > tol]))
        susy_pert = s0_p - s1_p + s2_p - s3_p
        self.assertLess(abs(susy_pert), 1e-12, "Metric perturbed SUSY trace sum must remain zero")

    def test_05_non_nilpotent_perturbation_breakdown(self):
        tiles1 = generate_supertile_tiles(FR30, 1)
        d0, d1, d2, _ = build_polyhedral_chair_complex(tiles1)

        rng = np.random.RandomState(42)
        eps = 0.05
        d1_bad = d1.toarray() + eps * rng.randn(*d1.shape)

        # Nilpotency fails
        nilp_bad = np.max(np.abs(d1_bad @ d0.toarray()))
        self.assertGreater(nilp_bad, 0.1)

        D0_b = d0.toarray().T @ d0.toarray()
        D1_b = d0.toarray() @ d0.toarray().T + d1_bad.T @ d1_bad
        D2_b = d1_bad @ d1_bad.T + d2.toarray().T @ d2.toarray()
        D3_b = d2.toarray() @ d2.toarray().T

        tol = 1e-7
        evs_b = [np.sort(eigh(D, eigvals_only=True)) for D in (D0_b, D1_b, D2_b, D3_b)]
        s0_b = np.sum(np.sqrt(np.maximum(0, evs_b[0][evs_b[0] > tol])))
        s1_b = np.sum(np.sqrt(np.maximum(0, evs_b[1][evs_b[1] > tol])))
        s2_b = np.sum(np.sqrt(np.maximum(0, evs_b[2][evs_b[2] > tol])))
        s3_b = np.sum(np.sqrt(np.maximum(0, evs_b[3][evs_b[3] > tol])))
        susy_bad = s0_b - s1_b + s2_b - s3_b
        self.assertGreater(abs(susy_bad), 0.5, "Non-nilpotent perturbation must break the SUSY trace sum")


class TestAdversarialLambda7PeriodicCrystal(unittest.TestCase):
    """Domain 5: Space-Filling Lambda_7 Periodic Crystal Gapless Packing & Det=7 Basis."""

    def test_01_z7_homomorphism_bijection(self):
        phi_vals = [homomorphic_map(u[0], u[1], u[2]) for u in U3]
        self.assertEqual(len(phi_vals), 7)
        self.assertEqual(set(phi_vals), set(range(7)), "phi must map U_3 bijectively onto Z_7")

        # Difference set (U_3 - U_3) intersect Lambda_7 = {0}
        diffs = [np.array(u1) - np.array(u2) for u1 in U3 for u2 in U3]
        self.assertEqual(len(diffs), 49)
        in_lambda = [d for d in diffs if (d[0] + 2 * d[1] + 4 * d[2]) % 7 == 0]
        self.assertEqual(len(in_lambda), 7, "Exactly 7 differences can have residue 0 mod 7")
        self.assertTrue(all(np.array_equal(d, [0, 0, 0]) for d in in_lambda), "Only d = 0 can belong to Lambda_7")

    def test_02_lambda7_basis_properties(self):
        B = get_lambda7_basis()
        self.assertEqual(B.shape, (3, 3))
        det_B = int(round(np.linalg.det(B)))
        self.assertEqual(det_B, 7, f"Determinant of Lambda_7 basis must be exactly 7, got {det_B}")

        # Each row of B must satisfy the kernel condition
        for row in B:
            self.assertEqual(homomorphic_map(row[0], row[1], row[2]), 0, f"Basis vector {row} must be in Ker(phi mod 7)")

    def test_03_lattice_membership_oracle_and_covering(self):
        B = get_lambda7_basis()
        B_mat = B.T  # columns are b1, b2, b3
        B_inv = np.linalg.inv(B_mat)

        phi_to_u = {homomorphic_map(u[0], u[1], u[2]): np.array(u) for u in U3}

        # Test 20,000 random integer points in Z^3
        rng = np.random.RandomState(42)
        test_pts = rng.randint(-150, 150, size=(20000, 3))

        for pt in test_pts:
            r = homomorphic_map(pt[0], pt[1], pt[2])
            u = phi_to_u[r]
            t = pt - u
            self.assertEqual(homomorphic_map(t[0], t[1], t[2]), 0, "Translation vector t must belong to Lambda_7")
            c = B_inv @ t
            self.assertTrue(
                np.allclose(c, np.round(c), atol=1e-10),
                f"Translation t={t} must be an integer linear combination of basis B"
            )

    def test_04_crystal_overlap_free_scaling(self):
        for lvl in (1, 2, 3):
            tiles = generate_lambda7_periodic_chairs(lvl)
            n_tiles = len(tiles)
            expected_cubes = 7 * n_tiles

            all_cubes = [c for _, _, cs in tiles for c in cs]
            unique_cubes = set(all_cubes)
            self.assertEqual(len(all_cubes), expected_cubes)
            self.assertEqual(
                len(unique_cubes), expected_cubes,
                f"Level {lvl} periodic crystal must have zero overlapping cubes"
            )

    def test_05_crystal_vs_chair44_holonomy_contrast(self):
        tiles_p1 = generate_lambda7_periodic_chairs(1)
        hol_p, _ = analyze_clifford_q8_connection(tiles_p1)
        # All orientations M_a = I => all holonomies are identically +1
        self.assertEqual(len(hol_p), 1, "Periodic crystal must yield only one holonomy class")
        self.assertIn("+1", hol_p, "Periodic crystal holonomy must be strictly trivial (+1)")

        # In sharp contrast, Chair44 Level-1 superchair has rich non-trivial holonomy
        tiles_c1 = generate_supertile_tiles(FR30, 1)
        hol_c, _ = analyze_clifford_q8_connection(tiles_c1)
        n_nontriv = sum(v for k, v in hol_c.items() if k != "+1")
        self.assertGreater(n_nontriv, 15, "Chair44 superchair must generate abundant non-trivial Q_8 holonomies")


if __name__ == "__main__":
    unittest.main()
