"""Tests for Phase VI (audit/phase6_gauge_audit.py, audit/phase6_forced_flux.py): the gauge structure theorems G1-G4, the forced-
flux lemma F'.1, the zero-mode dichotomy, the certified uniform floor on sample decorations, gauge invariance of dynamics, and
agreement of the independent plaquette census with the Lean-certified closed form.  Run: python -m unittest tests/test_phase6.py"""
import os, sys, re, unittest, itertools, collections
from fractions import Fraction
import numpy as np, scipy.linalg as sla
HERE = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.dirname(HERE); sys.path.insert(0, os.path.join(ROOT, 'audit'))
import phase6_gauge_audit as G
import phase6_forced_flux as F


def build(frames, level):
    tl = G.tiles(frames, level); pn = G.panels(tl); links = [G.link(tl[a][0], tl[b][0], k) for a, b, k, _ in pn]
    deg = np.zeros(len(tl))
    for a, b, k, _ in pn: deg[a] += 1; deg[b] += 1
    return tl, pn, links, deg


class TestGaugeStructure(unittest.TestCase):
    @classmethod
    def setUpClass(cls): cls.tl, cls.pn, cls.links, cls.deg = build(G.FR30, 2)

    def test_G1_lab_gauge_form(self):
        e = np.eye(3); gl = [G.su2_lift(M) for M, _ in self.tl]
        for (a, b, k, _), C in zip(self.pn, self.links):
            self.assertLess(np.abs(gl[a] @ C @ gl[b].conj().T - G.s(e[k]) @ gl[a] @ gl[b].conj().T @ G.s(e[k])).max(), 1e-12)

    def test_G2_corner_factorization(self):
        gl = [G.su2_lift(M) for M, _ in self.tl]; _, cyc = G.tree_and_cycles(len(self.tl), self.pn)
        for c in cyc: self.assertLess(np.abs(G.holonomy(self.pn, self.links, c) - G.corner_form(self.tl, self.pn, c, gl)).max(), 1e-12)

    def test_G3_axis_subgraphs_are_pure_gauge(self):
        e = np.eye(3)
        for (a, b, k, _), C in zip(self.pn, self.links):
            ga, gb = 1j * G.s(self.tl[a][0].T @ e[k]), 1j * G.s(self.tl[b][0].T @ e[k])
            self.assertAlmostEqual(np.linalg.det(ga), 1); self.assertLess(np.abs(ga.conj().T @ C @ gb - G.I2).max(), 1e-12)

    def test_G4_holonomy_group_is_Q8_and_links_in_Q8(self):
        self.assertTrue(all(G.q8name(C) is not None for C in self.links))
        _, cyc = G.tree_and_cycles(len(self.tl), self.pn)
        self.assertEqual({G.qclass(G.holonomy(self.pn, self.links, c)) for c in cyc}, {'+1', '-1', 'traceless'})

    def test_gauge_covariance_of_holonomy_and_invariance_of_dynamics(self):
        rng = np.random.default_rng(1)
        def rsu2():
            q = rng.normal(size=4); q /= np.linalg.norm(q); return q[0] * G.I2 - 1j * (q[1] * G.SIG[0] + q[2] * G.SIG[1] + q[3] * G.SIG[2])
        g = [rsu2() for _ in self.tl]; lg = [g[a] @ C @ g[b].conj().T for (a, b, k, _), C in zip(self.pn, self.links)]
        _, cyc = G.tree_and_cycles(len(self.tl), self.pn)
        for c in cyc[:200]:
            self.assertAlmostEqual(np.trace(G.holonomy(self.pn, self.links, c)).real, np.trace(G.holonomy(self.pn, lg, c)).real, places=12)
        n = len(self.tl); H0 = G.operator(self.tl, self.pn, self.links, np.full(n, 24.0)).toarray(); Hg = G.operator(self.tl, self.pn, lg, np.full(n, 24.0)).toarray()
        U0, Ug = sla.expm(-1j * 0.9 * H0), sla.expm(-1j * 0.9 * Hg)
        for a in range(0, n, 7):
            for b in range(n):
                self.assertAlmostEqual(np.sum(np.abs(U0[2*a:2*a+2, 2*b:2*b+2]) ** 2), np.sum(np.abs(Ug[2*a:2*a+2, 2*b:2*b+2]) ** 2), places=12)


class TestZeroModeDichotomy(unittest.TestCase):
    def test_free_laplacian_zero_iff_pure_gauge(self):
        tl, pn, links, deg = build(G.FR30, 2); n = len(tl)
        lam = lambda lk: np.linalg.eigvalsh(G.operator(tl, pn, lk, deg).toarray())[:3]
        w = lam(links); self.assertGreater(w[0], 4.7)                                   # FR30: not pure gauge -> gapped
        w = lam([G.I2] * len(pn)); self.assertLess(abs(w[0]) + abs(w[1]), 1e-10); self.assertGreater(w[2], 1e-3)   # trivial: 2 zero modes
        rng = np.random.default_rng(2); g = [sla.expm(1j * sum(x * S for x, S in zip(rng.normal(size=3), G.SIG))) for _ in range(n)]
        w = lam([g[a] @ g[b].conj().T for a, b, k, _ in pn]); self.assertLess(abs(w[0]) + abs(w[1]), 1e-10)   # pure gauge: 2 zero modes


class TestForcedFlux(unittest.TestCase):
    def test_lemma_F1_two_cycle_holonomy_formula(self):
        """W(a->b via e_k panel, b->a via e_l panel) is conjugate to det(M_a)det(M_b) s(M_b^T e_m) s(M_a^T e_m), m the third axis."""
        rng = np.random.default_rng(3); perms = list(itertools.permutations(range(3))); e = np.eye(3)
        for _ in range(200):
            Ma = np.diag(rng.choice([-1, 1], 3)) @ G.P(perms[rng.integers(6)]); Mb = np.diag(rng.choice([-1, 1], 3)) @ G.P(perms[rng.integers(6)])
            k, l = rng.choice(3, 2, replace=False); m = 3 - k - l
            W = G.link(Ma, Mb, k) @ G.link(Ma, Mb, l).conj().T
            eps = round(np.linalg.det(Ma)) * round(np.linalg.det(Mb))            # det factors: the corner identity uses M^T(u x v) = det(M) (M^T u x M^T v)
            V = eps * G.s(Mb.T @ e[m]) @ G.s(Ma.T @ e[m])
            self.assertAlmostEqual(np.trace(W).real, np.trace(V).real, places=12)

    def test_every_decoration_sample_is_not_pure_gauge_and_certified(self):
        c = Fraction(167, 100)
        for i in (0, 1, 4752, 6255, 6560, 3697, 1387):
            dec = F.decoration(i); tl, pn, links, deg = build(dec, 1)
            _, cyc = G.tree_and_cycles(len(tl), pn)
            self.assertTrue(any(G.qclass(G.holonomy(pn, links, cy)) != '+1' for cy in cyc))
            L = G.operator(tl, pn, links, deg).toarray()
            self.assertTrue(F.exact_posdef(np.rint(L.real).astype(int), np.rint(L.imag).astype(int), c))
        self.assertEqual(F.decoration(4752), G.FR30)

    def test_identity_frames_are_pure_gauge(self):
        tl, pn, _, deg = build(G.FR30, 1); tl = [(np.eye(3, dtype=int), cs) for _, cs in tl]
        links = [G.link(tl[a][0], tl[b][0], k) for a, b, k, _ in pn]
        self.assertTrue(all(np.abs(C - G.I2).max() < 1e-12 for C in links))


class TestLeanCensusAgreement(unittest.TestCase):
    def test_level3_census_matches_certified_closed_form(self):
        with open(os.path.join(ROOT, 'certificates', 'TypeSubstitutionCertificate.lean'), encoding='utf-8') as fh: src = fh.read()
        lst = lambda nm: [int(x) for x in re.search(r'def %s : List (?:Int|Nat) := \[([^\]]*)\]' % nm, src).group(1).split(',')]
        cls = lst('plaqClassCert'); W = [lst(n) for n in ('W8L', 'W4L', 'W2L', 'W1L')]; NP, D, m = 49, 64, 3
        cnt = collections.Counter()
        for q in range(108):
            v = 8 ** m * W[0][NP + q] + 4 ** m * W[1][NP + q] + 2 ** m * W[2][NP + q] + W[3][NP + q]
            cnt['+1' if cls[q] == 0 else '-1' if cls[q] == 1 else 'traceless'] += v
        lean = {k: v // D for k, v in cnt.items()}
        tl, pn, links, _ = build(G.FR30, 3)
        self.assertEqual(G.plaquette_census(tl, pn, links), lean)


if __name__ == '__main__':
    unittest.main()
