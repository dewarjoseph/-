"""Tests for Phase V-E (audit/phase5e_rg.py): the theorems E0-E6 of deliverables/PHASE5E_THEORETICAL_CONJECTURE.md checked on
small systems, the pole representation, the compressed root solver and gauge covariance.  Run: python -m unittest tests/test_phase5e.py"""
import os, sys, unittest
import numpy as np, scipy.linalg as sla
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, os.path.join(os.path.dirname(HERE), 'audit'))
import phase5e_rg as rg, phase5d_schur as d
from independent_clifford_q8_audit import FR30, tiles_at_level, panel_edges
import phase5b_sweep as sw


class TestGeometry(unittest.TestCase):
    def test_E0_graph_is_decoration_independent(self):
        def geo(dec):
            tiles = tiles_at_level(dec, 3); _, e = panel_edges(tiles)
            key = [min(t[2]) for t in tiles]
            return sorted(tuple(sorted(t[2])) for t in tiles), sorted((min(key[a], key[b]), max(key[a], key[b]), int(np.argmax(n))) for a, b, n, _, _ in e)
        ref = geo(FR30)
        for i in (0, 950, 3697, 6560): self.assertEqual(geo(sw.decoration(i)), ref)

    def test_face_count_is_level_independent(self):
        counts = [sum(len(rg.System(FR30, L).groups(c, 'face')) for c in range(8)) for L in (3, 4)]
        self.assertEqual(counts[0], counts[1])


class TestSchurTheorems(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.s = rg.System(950, 3); cls.w, cls.V = np.linalg.eigh(cls.s.H.toarray()); cls.E0 = cls.w[0]

    def test_pole_representation_equals_direct_solve(self):
        G = d.Glued(self.s.H, self.s.child, self.s.surf); E = 7.3
        for c, R in enumerate(G.R(E)): self.assertLess(np.abs(R - self.s.R(c, E)).max(), 1e-11)

    def test_E1_inertia_on_and_beyond_admissible_window(self):
        lamI = np.concatenate(self.s.lam)
        for E in (self.E0 - 0.3, self.E0 + 0.5, self.s.lam_II + 0.37, self.s.lam_II + 2.11):
            if np.min(np.abs(lamI - E)) < 1e-6: continue
            nK = int((np.linalg.eigvalsh(self.s.K(E)) < 0).sum())
            self.assertEqual(int((self.w < E).sum()), int((lamI < E).sum()) + nK)

    def test_E1_kernel_isomorphism_and_multiplicity(self):
        K = self.s.K(self.E0); mu, U = np.linalg.eigh(K)
        self.assertEqual(int((np.abs(mu) < 1e-9).sum()), 2)                 # one Kramers pair <-> 2-dim kernel
        psi = self.V[:, 0]; PS = psi[self.s.sS]; self.assertLess(np.linalg.norm(K @ PS), 1e-9)

    def test_E1_strict_edge_below_interior(self):
        self.assertLess(self.E0, self.s.lam_II)

    def test_E1_slope_and_concavity(self):
        red = rg.Reduced(self.s, rg.P_exact(self.s)); Es = np.linspace(self.E0 - 1, self.E0 + 1, 5); g = np.array([red.g(E) for E in Es])
        self.assertTrue(np.all(np.diff(g) <= -(Es[1] - Es[0]) + 1e-9))
        self.assertTrue(np.all(np.diff(g, 2) <= 1e-9))

    def test_E3_bounds_for_every_family(self):
        for fam, k in [('child', 2), ('face', 1), ('iface2', 1), ('fec', 1), ('patch2', 1), ('interface', None)]:
            red = rg.Reduced(self.s, rg.make_basis(self.s, fam, k)); E, _ = red.root(); gd = red.g(self.E0)
            self.assertGreaterEqual(E - self.E0, -1e-10); self.assertLessEqual(E - self.E0, gd + 1e-10)

    def test_E4_two_sided_capture_bound_and_mu2(self):
        K = self.s.K(self.E0); mu = np.linalg.eigvalsh(K); mu2 = mu[2]; mumax = mu[-1]
        lam3 = [x for x in self.w if x - self.E0 > 1e-7][0]
        self.assertGreaterEqual(mu2 + 1e-9, min(lam3, self.s.lam_II) - self.E0)
        self.assertLessEqual(mumax, 48 - self.E0 + 1e-9)
        psi = rg.kramers_pair(self.V[:, 0])
        for fam, k in [('child', 4), ('face', 2), ('fec', 2), ('interface', None)]:
            red = rg.Reduced(self.s, rg.make_basis(self.s, fam, k)); c, _ = rg.captured(self.s, red, psi); gd = red.g(self.E0)
            self.assertLessEqual(mu2 * (1 - c), gd + 1e-9); self.assertLessEqual(gd, mumax * (1 - c) / c + 1e-9)

    def test_exact_basis_root_is_the_bottom(self):
        for L in (2, 3):
            s = rg.System(FR30, L); w0 = np.linalg.eigvalsh(s.H.toarray())[0]
            self.assertLess(abs(rg.Reduced(s, rg.P_exact(s)).root()[0] - w0), 1e-9)

    def test_root_solver_matches_bisection(self):
        red = rg.Reduced(self.s, rg.make_basis(self.s, 'child', 4)); E, _ = red.root()
        lo, hi = self.E0 - 1, self.s.lam_II - 1e-6
        for _ in range(100):
            m = 0.5 * (lo + hi)
            if red.g(m) > 0: lo = m
            else: hi = m
        self.assertLess(abs(E - 0.5 * (lo + hi)), 1e-9)

    def test_reduced_spectra_are_kramers_degenerate(self):
        for fam, k in [('child', 3), ('face', 2), ('iface2', 2)]:
            w = np.linalg.eigvalsh(rg.Reduced(self.s, rg.make_basis(self.s, fam, k)).M(7.5))
            self.assertLess(np.abs(w[0::2] - w[1::2]).max(), 1e-9)


class TestGauge(unittest.TestCase):
    def test_E2_every_family_is_gauge_invariant(self):
        s0, s1 = rg.System(FR30, 3), rg.System(FR30, 3, gauge_seed=5)
        for fam, k in [('child', 2), ('face', 2), ('iface2', 1), ('fec', 1), ('patch2', 1), ('patch3', 1), ('interface', None)]:
            e0 = rg.Reduced(s0, rg.make_basis(s0, fam, k)).root()[0]; e1 = rg.Reduced(s1, rg.make_basis(s1, fam, k)).root()[0]
            self.assertLess(abs(e0 - e1), 1e-8, fam)

    def test_E2_splitting_a_kramers_pair_breaks_invariance(self):
        def odd_basis(s):                                                   # 3 vectors = one and a half Kramers pairs per child
            return [np.linalg.eigh(s.Rref(c))[1][:, :3] for c in range(8)]
        s0, s1 = rg.System(FR30, 3), rg.System(FR30, 3, gauge_seed=5)
        e0 = rg.Reduced(s0, odd_basis(s0)).root()[0]; e1 = rg.Reduced(s1, odd_basis(s1)).root()[0]
        self.assertGreater(abs(e0 - e1), 1e-6)


class TestHierarchy(unittest.TestCase):
    def test_E6_edge_is_monotone_in_level(self):
        for spec in (FR30, 950):
            E = [np.linalg.eigvalsh(rg.System(spec, L).H.toarray())[0] for L in (1, 2, 3)]
            self.assertTrue(E[1] < E[0] and E[2] < E[1])


if __name__ == '__main__':
    unittest.main()
