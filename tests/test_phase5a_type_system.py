"""
Phase 5a / Task A2 -- executable adversarial tests of the intrinsic type system (49 panel / 108 plaquette types).
Every test recomputes its numbers by running audit/phase5a_type_system_audit.py functions; nothing is pinned to a
stored fixture except the published level-1 class counts 60/26/3/31 that the boundary-perturbation test must break.
Run from the repository root:  python3 -m unittest tests/test_phase5a_type_system.py   or   python3 -I -m pytest -q tests/test_phase5a_type_system.py
"""
import os, sys, unittest, collections
import numpy as np
ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
sys.path.insert(0, os.path.join(ROOT, "audit"))
import phase5a_type_system_audit as A


class TestA_Representatives(unittest.TestCase):
    def test_type_system_size_and_distinctness(self):
        self.assertEqual(len(A.PTYPES), 49); self.assertEqual(len(A.QTYPES), 108)
        self.assertTrue(A.representatives_pairwise_distinct())

    def test_panel_representatives_valid_and_recompute(self):
        r = A.check_panel_representatives()
        self.assertEqual(r['n'], 49)
        self.assertEqual(r['invalid_config'], []); self.assertEqual(r['key_mismatch'], [])
        self.assertEqual(r['reconstruction_fail'], []); self.assertEqual(r['not_gamma_equivalent'], [])

    def test_plaquette_representatives_valid_and_recompute(self):
        r = A.check_plaquette_representatives()
        self.assertEqual(r['n'], 108)
        self.assertEqual(r['invalid_config'], []); self.assertEqual(r['key_mismatch'], []); self.assertEqual(r['class_mismatch'], [])
        self.assertEqual(r['reconstruction_fail'], []); self.assertEqual(r['not_gamma_equivalent'], [])
        self.assertEqual(sum(r['distinct_tiles_hist'].values()), 108)
        self.assertTrue(all(k in (2, 3, 4) for k in r['distinct_tiles_hist']))

    def test_lean_certificate_data_matches_python_representatives(self):
        r = A.lean_certificate_reps_match()
        if not r['present']: self.skipTest("certificates/TypeSubstitutionCertificate.lean not present")
        self.assertEqual(r['lean_panel_reps'], 49); self.assertEqual(r['lean_plaq_reps'], 108)
        self.assertTrue(r['panel_match']); self.assertTrue(r['plaq_match'])

    def test_tiling_matches_independent_construction(self):
        for m in (1, 2, 3): self.assertTrue(A.same_tiling_as_independent(m), m)


class TestB_Coverage(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.cov = {m: A.coverage_level(m, check_images=(m == 2)) for m in (1, 2, 3)}

    def test_every_instance_has_a_representative_key(self):
        for m, r in self.cov.items():
            self.assertEqual(r['panel_unknown'], 0, m); self.assertEqual(r['plaq_unknown'], 0, m)

    def test_distinct_key_counts_per_level(self):
        self.assertEqual((self.cov[1]['panels'], self.cov[1]['panel_types']), (48, 33))
        self.assertEqual((self.cov[1]['plaquettes'], self.cov[1]['plaq_types']), (60, 49))
        self.assertEqual((self.cov[2]['panels'], self.cov[2]['panel_types']), (576, 49))
        self.assertEqual((self.cov[2]['plaquettes'], self.cov[2]['plaq_types']), (792, 88))
        self.assertEqual((self.cov[3]['cubes'], self.cov[3]['panels'], self.cov[3]['panel_types']), (3584, 5376, 49))
        self.assertEqual((self.cov[3]['plaquettes'], self.cov[3]['plaq_types']), (7728, 108))
        self.assertEqual(self.cov[3]['_panel_keys'], A.PSET); self.assertEqual(self.cov[3]['_plaq_keys'], A.QSET)

    def test_class_and_link_label_are_functions_of_type(self):
        for m, r in self.cov.items():
            self.assertEqual(r['class_conflicts'], 0, m); self.assertEqual(r['link_label_conflicts'], 0, m)

    def test_counts_match_recursion(self):
        for m, r in self.cov.items():
            self.assertTrue(r['class_counts_match_recursion'], m)
            self.assertTrue(r['panel_type_counts_match_recursion'], m); self.assertTrue(r['plaq_type_counts_match_recursion'], m)
        self.assertEqual(self.cov[1]['class_counts'], {'1': 26, '-1': 3, 'i': 12, 'j': 7, 'k': 12})

    def test_inflation_images_well_defined_on_all_level2_instances(self):
        r = self.cov[2]
        self.assertEqual(r['image_checked_panels'], 576); self.assertEqual(r['image_bad_panels'], 0)
        self.assertEqual(r['image_checked_plaqs'], 792); self.assertEqual(r['image_bad_plaqs'], 0)


class TestC_Invariance(unittest.TestCase):
    def test_all_24_rotations_and_random_motions(self):
        r = A.invariance_test(n_random=50, seed=7)
        self.assertEqual(r['panel_SO3_checks'], 49*24); self.assertEqual(r['plaq_SO3_checks'], 108*24)
        self.assertEqual(r['panel_RAND_checks'], 49*50); self.assertEqual(r['plaq_RAND_checks'], 108*50)
        for k in ('panel_SO3_fail', 'plaq_SO3_fail', 'panel_RAND_fail', 'plaq_RAND_fail', 'plaq_SO3_class_fail', 'plaq_RAND_class_fail'):
            self.assertEqual(r[k], 0, k)
        self.assertTrue(r['ok_proper'])
        # the ambient (non-intrinsic) key changes under essentially every motion
        self.assertEqual(r['ambient_panel_RAND_changed'], 49*50)
        self.assertGreaterEqual(r['ambient_panel_SO3_changed'], 49*23)

    def test_key_invariant_under_improper_elements_too(self):
        # documented fact, not a defect: det=-1 frames never occur in the tiling, so equal key <=> SO(3,Z)xZ^3 related
        r = A.invariance_test(n_random=0, seed=1)
        self.assertEqual(r['panel_REFL_fail'], 0); self.assertEqual(r['plaq_REFL_fail'], 0)

    def test_rigid_motion_helpers_are_lattice_motions(self):
        rng = np.random.default_rng(0)
        for R in A.SO3Z + A.REFL:
            s = rng.integers(-5, 6, size=3)
            for _ in range(5):
                c = tuple(int(v) for v in rng.integers(-9, 10, size=3))
                for ax in range(3):
                    c2 = tuple(int(v) for v in np.asarray(c) + A.E[ax])
                    d = np.asarray(A.move_cube(R, s, c2)) - np.asarray(A.move_cube(R, s, c))
                    self.assertEqual(int(np.abs(d).sum()), 1)   # adjacent cubes stay adjacent
            G = R @ np.eye(3, dtype=int); T = np.array([3, -2, 5])
            moved = set(A.cubes(*A.move_pose(R, s, (G, T)))); direct = {A.move_cube(R, s, c) for c in A.cubes(G, T)}
            self.assertEqual(moved, direct)      # moving the pose = moving its cubes


class TestD_Orientation(unittest.TestCase):
    def test_representatives(self):
        r = A.orientation_test_reps()
        self.assertEqual(r['plaquettes'], 108); self.assertNotIn('class_changed', r); self.assertNotIn('non_q8', r)
        self.assertEqual(r['reversal_is_inverse'], 108); self.assertEqual(r['base_change_is_conjugation'], 108)
        self.assertNotIn('sign_varies_1', r); self.assertNotIn('sign_varies_-1', r)

    def test_level2_all_984(self):
        r = A.orientation_test_level(2)
        self.assertEqual(r['all_four_present']['plaquettes'], 984); self.assertEqual(r['inter_tile']['plaquettes'], 792)
        for key in ('all_four_present', 'inter_tile'):
            self.assertNotIn('class_changed', r[key]); self.assertNotIn('non_q8', r[key])
            self.assertEqual(r[key]['reversal_is_inverse'], r[key]['plaquettes'])
            self.assertEqual(r[key]['base_change_is_conjugation'], r[key]['plaquettes'])
        # the sign of a traceless holonomy DOES depend on the ordering (so only the class is an observable)
        self.assertEqual(r['inter_tile']['sign_varies_i'], 124); self.assertEqual(r['inter_tile']['sign_varies_j'], 117)
        self.assertEqual(r['inter_tile']['sign_varies_k'], 124)
        self.assertEqual(r['inter_tile']['constant_label_1'], 385); self.assertEqual(r['inter_tile']['constant_label_-1'], 42)


class TestE_Gauge(unittest.TestCase):
    def test_q8_and_su2_gauge_level2(self):
        g = A.gauge_test(2, seed=3, n_rounds=2)
        self.assertEqual(g['inter_tile_links'], 576); self.assertEqual(g['plaquettes_checked'], 984)
        self.assertTrue(g['ok']); self.assertTrue(g['links_change_under_gauge'])
        for r in g['rounds']:
            self.assertEqual(r['q8_classes_changed'], 0); self.assertEqual(r['q8_non_q8_holonomies'], 0)
            self.assertGreater(r['q8_signed_labels_changed'], 0)        # signed labels are gauge dependent
            self.assertEqual(r['su2_links_changed'], 576); self.assertEqual(r['su2_links_still_in_q8'], 0)
            self.assertLess(r['su2_max_trace_deviation'], 1e-9)


class TestF_NegativeControls(unittest.TestCase):
    def test_normal_reversal_for_one_tile_is_a_central_gauge_transformation(self):
        # The task predicted that reversing the face normal for one tile changes the affected plaquette classes.
        # Executing it shows the opposite: it negates every link incident to the tile (= gauge transformation by
        # -1 in the centre of Q8) and leaves every plaquette holonomy unchanged.  Reversing in both factors, or
        # globally, changes nothing at all.  We assert the ACTUAL behaviour.
        r = A.negative_normal_reversal(1, star_index=3)
        v = r['variants']['reverse_normal_in_star_factor']
        self.assertEqual(v['links_changed'], r['links_incident_to_star']); self.assertGreater(v['links_changed'], 0)
        self.assertEqual(v['plaquette_classes_changed'], 0); self.assertEqual(v['plaquette_signed_labels_changed'], 0)
        for kind in ('reverse_normal_both_factors_if_star', 'reverse_normal_globally'):
            self.assertEqual(r['variants'][kind]['links_changed'], 0); self.assertEqual(r['variants'][kind]['plaquette_classes_changed'], 0)

    def test_non_gauge_perturbations_of_one_tile_change_classes(self):
        r = A.negative_normal_reversal(1, star_index=3)
        for kind in ('forget_frame_of_star', 'permute_local_normal_of_star'):
            v = r['variants'][kind]
            self.assertGreater(v['plaquette_classes_changed'], 0, kind)
            self.assertLessEqual(v['plaquette_classes_changed'], v['plaquettes_touching_star'], kind)
            self.assertNotEqual(v['class_counts'], r['baseline_class_counts'], kind)

    def test_ambient_key_is_not_a_type_and_coarse_key_has_ill_defined_images(self):
        r = A.negative_ambient_key(2)
        self.assertEqual(r['intrinsic_panel_types_with_several_instances'], 49)
        self.assertEqual(r['intrinsic_types_whose_instances_have_different_ambient_keys'], 49)
        self.assertIsNotNone(r['example_equal_intrinsic_different_ambient'])
        self.assertGreater(r['coarse_panel_keys_with_conflicting_images'], 0)
        self.assertGreater(r['coarse_plaq_keys_with_conflicting_classes'], 0)

    def test_boundary_convention_perturbation_changes_level1_counts(self):
        r = A.negative_boundary_convention(1)
        self.assertEqual(r['strict_total'], 60); self.assertEqual(r['strict_1_m1_tr0'], (26, 3, 31))
        self.assertNotEqual(r['loose_total'], 60); self.assertNotEqual(r['loose_1_m1_tr0'], (26, 3, 31))
        self.assertGreater(r['extra_edges_counted_by_loose_convention'], 0)


class TestG_MissingNeighbours(unittest.TestCase):
    def test_edges_with_fewer_than_four_cubes_are_excluded(self):
        for m in (1, 2):
            r = A.missing_neighbour_census(m)
            self.assertTrue(r['phase4_equals_four_present_inter_tile'], m)
            self.assertGreater(r['excluded_lt4_present_touching_2plus_tiles'], 0, m)
            self.assertEqual(r['four_present_intra_tile'], 3 * 8**m, m)     # 3 interior edges per chair tile
        self.assertEqual(A.missing_neighbour_census(1)['four_present_inter_tile'], 60)
        self.assertEqual(A.missing_neighbour_census(2)['four_present_inter_tile'], 792)

    def test_source_conventions(self):
        sc = A.source_conventions()
        self.assertTrue(sc['phase4_seed_requires_all_four_present']); self.assertTrue(sc['phase4_returns_None_for_single_tile'])
        self.assertTrue(sc['lean_isInterTilePlaquette_requires_allPresent'])

    def test_plaquette_type_is_None_exactly_for_single_tile_edges(self):
        poses, om = A.build_level(1); n_none = n_some = 0
        for c in om:
            for (i, j) in ((0, 1), (0, 2), (1, 2)):
                cs = A.plaquette_cubes(c, i, j)
                if all(x in om for x in cs):
                    t, cl = A.ptc(om, c, i, j); single = len({A.key(*om[x]) for x in cs}) == 1
                    self.assertEqual(t is None, single); n_none += single; n_some += (not single)
        self.assertEqual((n_none, n_some), (24, 60))


if __name__ == "__main__":
    unittest.main()
