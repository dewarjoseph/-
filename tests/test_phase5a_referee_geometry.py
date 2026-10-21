"""
Tests for audit/phase5a_referee_geometry.py (levels 1..3, fast).

Checks the geometric statement for the FR30 chair substitution with an implementation that uses 3x3 integer
matrices (independent of the signed-permutation implementation in audit/phase5a_independent_enumerator.py), and
checks that the fill/disjointness test is sensitive to perturbations of the translation/reflection data while
being insensitive to the permutation table (only det +1 depends on the permutations).
Run:  python3 -u -I tests/test_phase5a_referee_geometry.py
"""
import os, unittest, importlib.util, itertools

ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
_spec = importlib.util.spec_from_file_location("phase5a_referee_geometry",
                                               os.path.join(ROOT, "audit", "phase5a_referee_geometry.py"))
RG = importlib.util.module_from_spec(_spec); _spec.loader.exec_module(RG)


class TestRefereeGeometry(unittest.TestCase):
    def test_child_operator_dets(self):
        for v in RG.U3:
            self.assertEqual(RG.int_det3(RG.D_s(v) @ RG.perm_matrix(RG.FR30[v])), 1)
            # parity bookkeeping of the deliverable: sgn(pi_v) = (-1)^|v|
            self.assertEqual(RG.int_det3(RG.perm_matrix(RG.FR30[v])), (-1) ** sum(v))

    def test_levels_1_to_3(self):
        ops = RG.make_rule()
        for m in (1, 2, 3):
            r, _ = RG.check_level(m, ops)
            self.assertEqual(r['tiles'], 8 ** m)
            self.assertEqual(r['distinct_cubes'], 7 * 8 ** m)
            self.assertEqual(r['overlapping_cubes'], 0)
            self.assertTrue(r['fills_chair_exactly'])
            self.assertTrue(r['all_frames_orthogonal'])
            self.assertEqual(r['frame_dets'], {1: 8 ** m})

    def test_fill_is_independent_of_permutations_but_det_is_not(self):
        swap = {v: (1, 0, 2) for v in RG.U3}   # all odd permutations
        r, _ = RG.check_level(2, RG.make_rule(perms=swap))
        self.assertTrue(r['fills_chair_exactly'] and r['pairwise_disjoint'])
        self.assertFalse(r['all_frames_det_plus1'])

    def test_perturbed_translations_break_the_fill(self):
        for kw in (dict(centre_offset=(1, 1, 0)), dict(octant_scale=2), dict(use_reflection=False)):
            r, _ = RG.check_level(1, RG.make_rule(**kw))
            self.assertFalse(r['fills_chair_exactly'] and r['pairwise_disjoint'])


if __name__ == '__main__':
    unittest.main()
