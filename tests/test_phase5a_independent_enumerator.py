"""
Tests for audit/phase5a_independent_enumerator.py (levels 1..3, fast).

The module under test imports nothing from audit/ or src/; it re-derives the class-resolved inter-tile plaquette
counts of the Clifford Q8 background on the FR30 chair substitution from the documented definitions, using signed
permutations and an abstract Q8 multiplication table.  The expected numbers below were obtained by running
    python3 -u -I audit/phase5a_independent_enumerator.py 3
in the session that wrote this file (output: audit/results/phase5a_independent_enumerator.txt); they coincide with
the recursion predictions in audit/results/phase4_type_substitution_proof.txt, with the straddling counts in
audit/results/phase3_straddle_closed_form_levels3-7.txt (level 3), and with certificates/Chair44GeometryToMatrix.lean
(level 1).
Run:  python3 -m unittest tests/test_phase5a_independent_enumerator.py
"""
import os, sys, unittest, importlib.util

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
_spec = importlib.util.spec_from_file_location("phase5a_independent_enumerator",
                                               os.path.join(ROOT, "audit", "phase5a_independent_enumerator.py"))
P5 = importlib.util.module_from_spec(_spec); _spec.loader.exec_module(P5)

EXPECTED_CLASSES = {
    1: {'1': 26, '-1': 3, 'i': 12, 'j': 7, 'k': 12},
    2: {'1': 385, '-1': 42, 'i': 124, 'j': 117, 'k': 124},
    3: {'1': 3945, '-1': 530, 'i': 1020, 'j': 1213, 'k': 1020},
}
EXPECTED_TOTAL_PLAQUETTES = {1: 84, 2: 984, 3: 9264}
EXPECTED_INTER_TILE = {1: 60, 2: 792, 3: 7728}
EXPECTED_STRADDLING = {1: 60, 2: 312, 3: 1392}
EXPECTED_STRADDLING_CLASSES = {
    1: {'1': 26, '-1': 3, 'i': 12, 'j': 7, 'k': 12},
    2: {'1': 177, '-1': 18, 'i': 28, 'j': 61, 'k': 28},
    3: {'1': 865, '-1': 194, 'i': 28, 'j': 277, 'k': 28},
}


class TestQ8AndFrames(unittest.TestCase):
    def test_q8_table_is_a_group_with_five_classes(self):
        cls = P5.q8_selfcheck()
        self.assertEqual(sorted(set(cls.values())), sorted(['1', '-1', 'i', 'j', 'k']))
        self.assertEqual(cls[(1, '1')], '1'); self.assertEqual(cls[(-1, '1')], '-1')
        self.assertEqual(cls[(1, 'i')], 'i'); self.assertEqual(cls[(-1, 'i')], 'i')

    def test_link_rule_parallel_antiparallel_perpendicular(self):
        i, j = P5.pure(0, 1), P5.pure(1, 1)
        self.assertEqual(P5.link_q(i, i), (1, '1'))
        self.assertEqual(P5.link_q(i, P5.qneg(i)), (-1, '1'))
        self.assertEqual(P5.link_q(i, j)[1], 'k')

    def test_signed_permutations_and_pauli(self):
        self.assertTrue(P5.signed_perm_selfcheck())
        self.assertTrue(P5.pauli_identity_check())

    def test_child_operators_have_det_plus1(self):
        for v in P5.U3:
            self.assertEqual(P5.sp_det(P5.sp_compose(P5.D_s(v), P5.P_of(P5.FR30[v]))), 1)


class TestEnumerationLevels1to3(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.levels = {m: P5.Level(m) for m in (1, 2, 3)}
        cls.vec = {m: L.plaquettes_vectorised() for m, L in cls.levels.items()}

    def test_geometry(self):
        for m, L in self.levels.items():
            self.assertEqual(L.ntiles, 8 ** m); self.assertEqual(L.ndistinct, 7 * 8 ** m)
            self.assertTrue(L.disjoint); self.assertTrue(L.fills_chair); self.assertTrue(L.all_det_plus1)

    def test_exact_class_counts(self):
        for m in (1, 2, 3):
            self.assertEqual(self.vec[m]['classes'], EXPECTED_CLASSES[m])
            self.assertEqual(self.vec[m]['plaquettes_total'], EXPECTED_TOTAL_PLAQUETTES[m])
            self.assertEqual(self.vec[m]['inter_tile'], EXPECTED_INTER_TILE[m])
            self.assertEqual(self.vec[m]['inter_tile'], 18 * 8 ** m - 24 * 4 ** m + 6 * 2 ** m)

    def test_straddling_counts(self):
        for m in (1, 2, 3):
            self.assertEqual(self.vec[m]['straddling'], EXPECTED_STRADDLING[m])
            self.assertEqual(self.vec[m]['straddling'], 24 * 4 ** m - 18 * 2 ** m)
            self.assertEqual(self.vec[m]['straddling_classes'], EXPECTED_STRADDLING_CLASSES[m])

    def test_scalar_evaluator_agrees(self):
        for m in (1, 2, 3):
            sc = self.levels[m].plaquettes_scalar()
            self.assertEqual(sc['classes'], EXPECTED_CLASSES[m])
            self.assertEqual(sc['plaquettes_total'], EXPECTED_TOTAL_PLAQUETTES[m])
            self.assertEqual(sc['inter_tile'], EXPECTED_INTER_TILE[m])

    def test_level1_matches_lean_certificate_numbers(self):
        pc = self.levels[1].panels_and_pauli_check()
        self.assertEqual(pc['shared_panels'], 48); self.assertTrue(pc['pauli_agrees_on_all_panels'])
        self.assertEqual(pc['link_values'], {'+1': 6, '-1': 24, 'traceless': 18})
        c = self.vec[1]['classes']
        self.assertEqual((c['1'], c['-1'], c['i'] + c['j'] + c['k']), (26, 3, 31))

    def test_level2_pauli_agreement(self):
        pc = self.levels[2].panels_and_pauli_check()
        self.assertEqual(pc['shared_panels'], 576); self.assertTrue(pc['pauli_agrees_on_all_panels'])
        self.assertEqual(pc['link_values'], {'+1': 90, '-1': 228, 'traceless': 258})


if __name__ == '__main__':
    unittest.main()
