"""Tests for audit/phase5a_flux_vs_edge.py (Task D1).  Run: python3 -m unittest tests/test_phase5a_flux_vs_edge.py"""
import os, sys, unittest
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, os.path.join(os.path.dirname(HERE), 'audit'))
import phase5a_flux_vs_edge as fe
from independent_clifford_q8_audit import FR30, tiles_at_level


class TestFluxVsEdge(unittest.TestCase):
    def test_q8_codes_form_group_table(self):
        T = fe.MUL
        self.assertEqual(T.shape, (8, 8))
        for a in range(8):
            self.assertEqual(sorted(T[a]), list(range(8)))       # Latin square rows
            self.assertEqual(sorted(T[:, a]), list(range(8)))
        self.assertTrue((T[0] == np.arange(8)).all())              # 0 is the identity

    def test_fr30_plaquette_classes_levels_1_2(self):
        expect = {1: (60, 26, 3, 31), 2: (792, 385, 42, 365)}
        for L, exp in expect.items():
            owners, hol = fe.plaquettes(tiles_at_level(FR30, L), L); f = fe.flux_fractions(hol)
            self.assertEqual((f['N'], f['n_plus'], f['n_minus'], f['n_traceless']), exp)

    def test_total_plaquette_count_is_geometric(self):
        # N_m = 18*8^m - 24*4^m + 6*2^m for any admissible decoration (geometry only)
        dec, _ = fe.random_decoration(1)
        for L in (1, 2):
            _, hol = fe.plaquettes(tiles_at_level(dec, L), L)
            self.assertEqual(len(hol), 18 * 8 ** L - 24 * 4 ** L + 6 * 2 ** L)

    def test_random_decoration_changes_classes(self):
        dec, _ = fe.random_decoration(1)
        _, h1 = fe.plaquettes(tiles_at_level(dec, 2), 2); _, h0 = fe.plaquettes(tiles_at_level(FR30, 2), 2)
        self.assertNotEqual(fe.flux_fractions(h1)['n_minus'], fe.flux_fractions(h0)['n_minus'])

    def test_organization_statistics_are_finite(self):
        tiles = tiles_at_level(FR30, 2); owners, hol = fe.plaquettes(tiles, 2)
        o = fe.organization(owners, hol, len(tiles), 2)
        for v in o.values(): self.assertTrue(np.isfinite(v))
        self.assertGreater(o['enr1_minus'], 0)


if __name__ == '__main__':
    unittest.main()
