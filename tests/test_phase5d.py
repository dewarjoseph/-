"""Tests for Phase V-D (audit/phase5d_schur.py).  Run: python3 -m unittest tests/test_phase5d.py"""
import os, sys, unittest
import numpy as np, scipy.linalg as sla, scipy.sparse as sps
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, os.path.join(os.path.dirname(HERE), 'audit'))
import phase5d_schur as d
from independent_clifford_q8_audit import FR30


class TestSchur(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tiles = d.tiles_of(FR30, 3); cls.H, cls.edges = d.build(cls.tiles)
        cls.child, cls.surf = d.partition(len(cls.tiles), cls.edges, 3); cls.G = d.Glued(cls.H, cls.child, cls.surf)
        cls.w = np.linalg.eigvalsh(cls.H.toarray())

    def test_interior_is_block_diagonal(self):
        Hd = self.H.toarray(); I = np.nonzero(~self.surf)[0]
        for a in I:
            for b in I:
                if self.child[a] != self.child[b]: self.assertEqual(np.abs(Hd[2*a:2*a+2, 2*b:2*b+2]).max(), 0)

    def test_root_equals_direct_bottom(self):
        E0, it = self.G.root(self.w[0] - 1, self.w[0] + 0.5)
        self.assertLess(abs(E0 - self.w[0]), 1e-9); self.assertAlmostEqual(self.w[0], 9.378470210, places=8)

    def test_inertia(self):
        for e in (8.0, 9.0, 9.5, 10.0, 12.0):
            self.assertLess(e, self.G.lam_II)
            self.assertEqual(int((self.w < e).sum()), int((np.linalg.eigvalsh(self.G.K(e)) < 0).sum()))

    def test_schur_matches_explicit_complement(self):
        e = 8.5; Hd = self.H.toarray() - e * np.eye(self.H.shape[0]); S = self.G.sS; I = np.setdiff1d(np.arange(Hd.shape[0]), S)
        Kx = Hd[np.ix_(S, S)] - Hd[np.ix_(S, I)] @ np.linalg.solve(Hd[np.ix_(I, I)], Hd[np.ix_(I, S)])
        self.assertLess(np.abs(Kx - self.G.K(e)).max(), 1e-11)

    def test_monotone_slope(self):
        a, b = self.G.lam_min(self.G.K(8.0))[0], self.G.lam_min(self.G.K(8.5))[0]
        self.assertLessEqual((b - a) / 0.5, -1 + 1e-9)          # d lambda_min / dE <= -1

    def test_gauge_invariance(self):
        rng = np.random.default_rng(3); Us = []
        for _ in range(len(self.tiles)):
            q = rng.normal(size=4); q /= np.linalg.norm(q)
            Us.append(np.array([[q[0] + 1j*q[3], q[2] + 1j*q[1]], [-q[2] + 1j*q[1], q[0] - 1j*q[3]]]))
        Gm = sps.block_diag(Us, format='csr'); Gg = d.Glued((Gm @ self.H @ Gm.conj().T).tocsr(), self.child, self.surf)
        f1, f2 = self.G.features(8.5), Gg.features(8.5)
        for k in f1:
            if k not in ('E', 'admissible') and not k.startswith('dim'): self.assertAlmostEqual(f1[k], f2[k], places=10)

    def test_reduced_model_is_upper_bound(self):
        f = self.G.features(8.5)
        for k in d.KS: self.assertGreaterEqual(f[f'g{k}'] + 1e-12, f['kmin'])


if __name__ == '__main__':
    unittest.main()
