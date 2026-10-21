"""Tests for Phase V-C (audit/phase5c_*.py).  Run: python3 -m unittest tests/test_phase5c.py"""
import os, sys, unittest
from fractions import Fraction
import numpy as np, scipy.linalg as sla
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, os.path.join(os.path.dirname(HERE), 'audit'))
import phase5c_q8_gauge as g
import phase5c_dirac as dr


class TestQ8(unittest.TestCase):
    def test_group_axioms(self):
        M = g.MUL
        for a in range(8):
            self.assertEqual(sorted(M[a]), list(range(8)))
            self.assertEqual(M[a, g.INV[a]], 0)
            for b in range(8):
                for c in range(8): self.assertEqual(M[M[a, b], c], M[a, M[b, c]])
        i, j, k = 2, 4, 6
        self.assertEqual(M[i, i], 1); self.assertEqual(M[M[i, j], k], 1)        # i^2 = ijk = -1

    def test_heat_bath_distribution(self):
        rng = np.random.default_rng(0); S = np.tile([0.7, -0.2, 0.4, 0.1], (200000, 1)); beta = 1.3
        x = g.heat_bath(S, beta, rng); emp = np.bincount(x, minlength=8) / len(x)
        w = np.exp(beta * (g.COEF @ S[0])); exact = w / w.sum()
        self.assertLess(np.abs(emp - exact).max(), 0.005)
        # COEF row g gives Re(g * s) for the quaternion product
        for a in range(8):
            self.assertAlmostEqual(g.COEF[a] @ S[0], g.qmul_vec(g.QV[a], S[0])[0], places=12)

    def test_engines_agree_and_strong_coupling(self):
        A = g.Periodic(3, 4, seed=1); nl, pl, fr = g.periodic_complex(4); B = g.General(nl, pl, fr, seed=2)
        pa, pb = [], []
        for it in range(300):
            A.sweep(0.6); B.sweep(0.6)
            if it >= 50: pa.append(g.RE[A.plaquettes()].mean()); pb.append(g.RE[B.plaquettes()].mean())
        self.assertLess(abs(np.mean(pa) - np.mean(pb)), 0.02)
        self.assertLess(abs(np.mean(pa) - 0.6 / 4), 0.02)          # <P> ~ beta/4 at strong coupling

    def test_fr30_connection_plaquette(self):
        self.assertAlmostEqual(g.FR30_P, 63 / 144, places=12)


class TestDirac(unittest.TestCase):
    def test_index_theorem_level1(self):
        for triv in (True, False):
            tiles, cells, index, U = dr.complex_cells(1, trivial=triv)
            d = [dr.coboundary(cells, index, U, k) for k in range(3)]
            chi = sum((-1) ** k * len(cells[k]) for k in range(4)); self.assertEqual(chi, 1)
            import scipy.sparse as sps
            Dp = sps.bmat([[d[0], d[1].conj().T], [None, d[2]]]).toarray()
            s = sla.svdvals(Dp); rank = int((s > 1e-9 * s.max()).sum())
            self.assertEqual((Dp.shape[1] - rank) - (Dp.shape[0] - rank), 2 * chi)
            curv = abs(d[1] @ d[0]).max()
            if triv: self.assertLess(curv, 1e-12); self.assertLess(abs(d[2] @ d[1]).max(), 1e-12)
            else: self.assertAlmostEqual(curv, 2.0, places=10)

    def test_dispersion_k1(self):
        import phase5a_periodic_approximants as pa, scipy.sparse as sps
        A = pa.Approximant(1)
        def w2(q):
            ph = np.exp(1j * (A.D @ q)); M = sps.coo_matrix((-ph, (A.rows, A.cols)), shape=(A.n, A.n)).toarray() + 24 * np.eye(A.n)
            return np.linalg.eigvalsh(M)[0]
        self.assertLess(abs(w2(np.zeros(3))), 1e-12)
        t = 0.01; vals = [w2(t * np.array(v) / np.linalg.norm(v)) / t ** 2 for v in ((1, 0, 0), (0, 1, 0), (1, 1, 1), (1, -1, 0))]
        self.assertLess(max(vals) - min(vals), 0.05); self.assertAlmostEqual(np.mean(vals), 14.97, delta=0.05)
        self.assertAlmostEqual(w2(np.array([0.03, -0.02, 0.01])), w2(-np.array([0.03, -0.02, 0.01])), places=12)   # no odd powers


class TestGap(unittest.TestCase):
    def test_certified_bracket(self):
        import phase5c_gap_scaling as gs
        self.assertGreater(gs.LOW, 4); self.assertLess(gs.UP, Fraction(8770134, 1000000))
        self.assertLess(gs.LOW, gs.UP); self.assertLessEqual(float(gs.UP), gs.PIN[6] + 1e-9)


if __name__ == '__main__':
    unittest.main()
