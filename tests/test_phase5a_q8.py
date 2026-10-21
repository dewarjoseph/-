"""
Tests for audit/phase5a_q8_conventions.py (Phase 5a / Task A4): Pauli-quaternion dictionary identities and the
base-point / orientation / Q8-gauge invariance of plaquette holonomy CLASSES at level 1 (plus the exact limiting
frequencies rebuilt from the Lean certificate data).  Every number is recomputed by the module under test; the only
values pinned here are the published level-1 class counts (26, 3, 12, 7, 12), the limiting frequencies
(19/36, 13/144, 1/9, 23/144, 1/9) and the documented frame-change counterexample, which the tests must reproduce.
Run from the repository root:  python3 -I -m pytest -q tests/test_phase5a_q8.py   or   python3 -m unittest tests/test_phase5a_q8.py
"""
import os, sys, unittest, importlib.util
from fractions import Fraction as Fr
import numpy as np

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)
_spec = importlib.util.spec_from_file_location("phase5a_q8_conventions", os.path.join(ROOT, "audit", "phase5a_q8_conventions.py"))
Q = importlib.util.module_from_spec(_spec); _spec.loader.exec_module(Q)


class TestQ8Table(unittest.TestCase):
    def test_table_is_the_quaternion_group(self):
        ax = Q.q8_group_axioms()
        for k in ('relations', 'closed', 'associative', 'identity', 'inverses', 'class_function_matches_orbits', 'classes_closed_under_inversion'):
            self.assertTrue(ax[k], k)
        self.assertEqual(ax['n_classes'], 5)
        self.assertEqual(sorted(ax['centre']), sorted([(1, '1'), (-1, '1')]))
        self.assertEqual({f"{x}{y}": Q.lab(Q.Q8TAB[(x, y)]) for x in 'ijk' for y in 'ijk' if x != y},
                         {'ij': '+k', 'ji': '-k', 'jk': '+i', 'kj': '-i', 'ki': '+j', 'ik': '-j'})

    def test_table_is_unique(self):
        found = Q.q8_uniqueness_by_exhaustion()
        self.assertEqual(len(found), 1)
        self.assertTrue(all(found[0][k] == Q.Q8TAB[k] for k in found[0]))


class TestDictionary(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.d = Q.check_dictionary()

    def test_e1e2_equals_e3_and_companions(self):
        for k in ('e1e2=e3', 'e2e3=e1', 'e3e1=e2', 'em^2=-1', 'e1e2e3=-1'):
            self.assertTrue(self.d[k], k)
        self.assertTrue(np.array_equal(Q.E[0] @ Q.E[1], Q.E[2]))

    def test_phi_is_an_injective_homomorphism_into_SU2(self):
        self.assertTrue(self.d['phi_homomorphism_64']); self.assertTrue(self.d['phi_injective']); self.assertTrue(self.d['phi_in_SU2'])

    def test_pauli_product_is_minus_quaternion_product_on_all_36_pairs(self):
        self.assertEqual(self.d['n_pairs'], 36)
        self.assertEqual(self.d['pauli_equals_minus_quaternion_product'], 36)

    def test_repo_integer_routine_agrees_on_all_36_pairs(self):
        self.assertEqual(self.d['repo_int_routine_agrees'], 36)
        self.assertEqual(self.d['repo_int_routine_disagreements'], [])

    def test_numpy_q8label_agrees_on_classes_but_flips_noncentral_signs(self):
        self.assertEqual(self.d['numpy_q8label_class_agrees'], 36)
        self.assertEqual(self.d['numpy_q8label_signed_agrees'], 12)       # the 12 central (+-1) products only
        self.assertTrue(self.d['q8label_plus_m_is_matrix_i_sigma_m']); self.assertTrue(self.d['i_sigma_m_is_quaternion_minus_m'])
        for ua, ub, mine, theirs in self.d['numpy_q8label_signed_disagreements']:
            self.assertEqual(mine[1:], theirs[1:]); self.assertNotEqual(mine[0], theirs[0])

    def test_lean_qmul_matches_derived_table(self):
        ok, _ = Q.lean_qmul_check(); self.assertTrue(ok)


class TestLevel1Invariances(unittest.TestCase):
    def test_reverse_normal_gives_inverse_and_dagger_on_all_48_links(self):
        L = Q.check_links_level1()
        self.assertEqual(L['n_links'], 48)
        self.assertEqual(L['reverse_normal_is_inverse'], 48); self.assertEqual(L['reverse_normal_is_dagger'], 48)
        self.assertEqual(L['repo_int_routine_agrees'], 48); self.assertEqual(L['numpy_matrix_agrees'], 48)
        self.assertEqual(L['link_classes']['1'], 6); self.assertEqual(L['link_classes']['-1'], 24)
        self.assertEqual(L['link_classes']['i'] + L['link_classes']['j'] + L['link_classes']['k'], 18)

    def test_plaquette_class_independent_of_basepoint_and_orientation(self):
        r = Q.check_plaquette_invariance(1)
        self.assertEqual(r['n_plaquettes'], 84); self.assertEqual(r['n_inter_tile'], 60)
        self.assertEqual(r['n_class_independent_of_basepoint_orientation'], 84)
        self.assertEqual(r['inter_tile_class_counts'], {'1': 26, '-1': 3, 'i': 12, 'j': 7, 'k': 12})
        self.assertGreater(r['n_inter_tile_with_varying_signed_label'], 0)       # signed labels are not invariants
        for ex in r['examples']:
            self.assertEqual(len(ex['classes']), 1); self.assertEqual(len(set(ex['labels_of_8_variants'])), 2)

    def test_q8_gauge_transformation_preserves_classes_not_labels(self):
        g = Q.check_q8_gauge(1)
        self.assertEqual(g['classes_equal'], g['n_inter_tile']); self.assertEqual(g['n_inter_tile'], 60)
        self.assertLess(g['signed_labels_equal'], g['n_inter_tile'])
        self.assertIsNotNone(g['example'])

    def test_su2_conjugation_preserves_trace_only(self):
        su = Q.check_su2_conjugation()
        self.assertEqual(su['U=(1+j)/sqrt2']['class_before'], 'i'); self.assertEqual(su['U=(1+j)/sqrt2']['class_after'], 'k')
        self.assertEqual(su['U=(1+j)/sqrt2']['trace_before'], su['U=(1+j)/sqrt2']['trace_after'])
        self.assertFalse(su['generic_U']['in_Q8']); self.assertAlmostEqual(abs(su['generic_U']['trace']), 0.0, places=9)

    def test_ambient_axis_label_is_basepoint_dependent_but_local_is_not(self):
        r = Q.check_ambient_relabeling(1)
        self.assertEqual(r['local_frame_classes'], {'1': 26, '-1': 3, 'i': 12, 'j': 7, 'k': 12})
        self.assertGreater(r['n_ambient_axis_depends_on_base_tile'], 0)
        self.assertEqual(r['spinlift_numeric_ok'], r['spinlift_numeric_checked']); self.assertEqual(r['spinlift_numeric_checked'], 31)


class TestCertificateLimits(unittest.TestCase):
    def test_frequencies_and_normalization_from_lean_data(self):
        data = Q.parse_lean_lists(); C = Q.certificate_limits(data)
        self.assertEqual((C['nP'], C['nQ']), (49, 108))
        self.assertEqual(C['lim_N_over_8m'], Fr(18))
        self.assertEqual(C['freqs'], {'1': Fr(19, 36), '-1': Fr(13, 144), 'i': Fr(1, 9), 'j': Fr(23, 144), 'k': Fr(1, 9)})
        self.assertEqual(C['trace0_freq'], Fr(55, 144))
        self.assertTrue(C['W8_over_D_equals_u']); self.assertTrue(C['residual_identity_ok'])
        for m in range(1, 8):
            self.assertEqual(C['recursion'][m]['plaquettes'], 18 * 8 ** m - 24 * 4 ** m + 6 * 2 ** m, m)
            self.assertEqual(C['recursion'][m]['panels'], 12 * (8 ** m - 4 ** m), m)
        self.assertEqual([C['recursion'][m]['plaquettes'] for m in range(1, 6)], [60, 792, 7728, 67680, 565440])


class TestDecorationDependence(unittest.TestCase):
    def test_frame_change_alters_classes_and_mirror_does_not(self):
        dm = Q.check_decoration_dependence_and_mirror()
        self.assertTrue(dm['classes_changed'])
        self.assertEqual(dm['fundamental_cycle_traces_before'], [(-2, 1), (0, 23), (2, 17)])
        self.assertEqual(dm['fundamental_cycle_traces_after'], [(-2, 1), (0, 22), (2, 18)])
        self.assertEqual(dm['mirror_links_equal_sigma1_C_sigma1'], 48); self.assertTrue(dm['mirror_classes_equal'])


if __name__ == '__main__':
    unittest.main()
