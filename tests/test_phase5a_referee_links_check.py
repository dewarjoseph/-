"""
Regression test for audit/phase5a_referee_links_check.py (referee path (R) only; fast, < 2 s).

The expected numbers are the ones the referee computed in this session with
    python3 -u -I audit/phase5a_referee_links_check.py
(output audit/results/phase5a_referee_links_check.txt).  They coincide with certificates/Chair44GeometryToMatrix.lean
(level 1: panels.length = 48, countLink qOne = 6, countLink -1 = 24, traceless 18), with
audit/results/phase2_structure_census.txt (level 2: |E| = 576) and with audit/results/phase5a_edge_states_level2.txt
(level 2: '+1': 90, '-1': 228, traceless 43+34+52+43+52+34 = 258).  This is a regression fixture, not an independent
verification.
Run:  python3 -u -I tests/test_phase5a_referee_links_check.py
"""
import os, unittest, importlib.util

ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
_spec = importlib.util.spec_from_file_location('phase5a_referee_links_check', os.path.join(ROOT, 'audit', 'phase5a_referee_links_check.py'))
RF = importlib.util.module_from_spec(_spec); _spec.loader.exec_module(RF)

EXPECTED = {1: (48, {'+1': 6, '-1': 24, 'traceless': 18, 'other': 0}),
            2: (576, {'+1': 90, '-1': 228, 'traceless': 258, 'other': 0})}


class TestRefereePath(unittest.TestCase):
    def test_levels_1_and_2(self):
        for lvl, (npan, vals) in EXPECTED.items():
            res, _ = RF.ref_level(lvl, RF.FR30, 'FR30')
            self.assertTrue(res['fills_chair_exactly']); self.assertEqual(res['frame_dets'], [1])
            self.assertEqual(res['shared_panels'], npan); self.assertEqual(res['shared_panels_from_face_count'], npan)
            self.assertEqual(res['link_values'], vals); self.assertTrue(res['all_links_in_Q8'])
            self.assertEqual(res['identity_minus_i_sigma_holds_on_panels'], npan)
            self.assertLess(res['identity_plus_i_sigma_holds_on_panels'], npan)
            self.assertTrue(res['value_class_orientation_independent']); self.assertTrue(res['value_class_normal_sign_independent'])

    def test_counts_are_decoration_dependent(self):
        res, _ = RF.ref_level(1, {v: (0, 1, 2) for v in RF.U3}, 'all_identity')
        self.assertEqual(res['shared_panels'], 48)
        self.assertNotEqual(res['link_values'], EXPECTED[1][1])


if __name__ == '__main__':
    unittest.main()
