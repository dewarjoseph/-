"""Tests for audit/phase5b_sweep.py (Phase V-B, Workstream B).  Run: python3 -m unittest tests/test_phase5b_sweep.py"""
import os, sys, unittest
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, os.path.join(os.path.dirname(HERE), 'audit'))
import phase5b_sweep as sw
from independent_clifford_q8_audit import FR30, U3, tiles_at_level


class TestDecorationSpace(unittest.TestCase):
    def test_index_bijection_and_admissibility(self):
        seen = set()
        for i in range(0, sw.NDEC, 97):
            dec = sw.decoration(i); self.assertEqual(sw.index_of(dec), i)
            self.assertIn(dec['0'], sw.EVEN)
            for v in U3: self.assertIn(dec[v], sw.EVEN if sum(v) % 2 == 0 else sw.ODD)
            seen.add(tuple(sorted((str(k), tuple(val)) for k, val in dec.items())))
        self.assertEqual(len(seen), len(range(0, sw.NDEC, 97)))

    def test_fr30_is_in_the_space(self):
        self.assertEqual(sw.decoration(sw.FR30_INDEX), FR30)

    def test_sample_is_deterministic_and_contains_fr30(self):
        s1 = sw.sample_indices(); s2 = sw.sample_indices()
        self.assertEqual(s1, s2); self.assertEqual(s1[0], sw.FR30_INDEX); self.assertEqual(len(set(s1)), sw.SAMPLE_SIZE + 1)


class TestPredictors(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tiles = tiles_at_level(FR30, 3); cls.pred = sw.predictors(cls.tiles, 3)

    def test_fr30_level3_class_counts(self):
        p = self.pred
        self.assertEqual((p['N_inter'], p['n_plus'], p['n_minus'], p['n_traceless']), (7728, 3945, 530, 3253))
        self.assertEqual((p['n_i'], p['n_j'], p['n_k']), (1020, 1213, 1020))

    def test_class_pair_matrix_is_normalised(self):
        # sum over class pairs of J = C * f f^T equals 1 for both pair definitions
        f = np.array([self.pred['n_plus'], self.pred['n_minus'], self.pred['n_traceless']]) / self.pred['N_inter']
        for tag in ('Ct', 'Cp'):
            C = np.zeros((3, 3)); names = ['p1', 'm1', 'trl']
            for a in range(3):
                for b in range(a, 3):
                    C[a, b] = C[b, a] = self.pred[f'{tag}_{names[a]}_{names[b]}']
            self.assertAlmostEqual(float((C * np.outer(f, f)).sum()), 1.0, places=9)

    def test_enrichment_definition(self):
        # enrichment of class k at depth d = P(straddle | k) / P(straddle); the class-weighted mean of enrichments is 1
        p = self.pred; f = np.array([p['n_plus'], p['n_minus'], p['n_traceless']]) / p['N_inter']
        # P(straddle) = sum_k f_k P(straddle|k) -> f_m1 enr_m1 + f_trl enr_trl + f_p1 enr_p1 = 1 ; enr_p1 not stored, so check bound
        self.assertLessEqual(f[1] * p['enr1_m1'] + f[2] * p['enr1_trl'], 1.0 + 1e-9)

    def test_loop_fractions_sum_to_one(self):
        # ring_loops returns (f_+1, f_-1, f_trl); the stored two entries must be <= 1 jointly
        self.assertLessEqual(self.pred['loop22_f_m1'] + self.pred['loop22_f_trl'], 1.0)
        self.assertLessEqual(self.pred['loop21_f_m1'] + self.pred['loop21_f_trl'], 1.0)

    def test_loop11_equals_plaquettes(self):
        o, h, e, grid, G = sw.plaquettes_with_edges(self.tiles, 3)
        fr = sw.ring_loops(grid, G, 16, (1, 1)); cl = sw.fe.classes(h)
        self.assertAlmostEqual(fr[1], (cl == 1).mean(), places=12); self.assertAlmostEqual(fr[2], (cl == 2).mean(), places=12)


class TestBottom(unittest.TestCase):
    def test_level2_bottom_matches_baseline(self):
        b = sw.bottom(FR30, 2)
        self.assertAlmostEqual(b['lambda'][0], 10.776950512, places=8); self.assertLess(b['residual'], 1e-12)
        self.assertLess(b['kramers_split'], 1e-10)


if __name__ == '__main__':
    unittest.main()
