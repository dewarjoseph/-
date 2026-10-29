#!/usr/bin/env python3
"""Phase XII: the machine-readable claims ledger -> audit/results/phase12_ledger.json.

Every claim: id, statement, status ([P] proved, [C] computer-certified, [E] floating-point evidence, [X] conjecture or
extrapolation, [F] falsified, open, not claimed), assumptions, evidence (artifact:key), test (tests/test_phase12.py names; a
'phase11:' prefix names a test of tests/test_phase11.py).  'corrections' lists the Phase XI statements found to exceed their
proofs (report section 1.3).  Values that depend on runs are read from the artifacts, not typed.
Usage: python -u -I audit/phase12_ledger.py"""
import os, json, subprocess
HERE = os.path.dirname(os.path.abspath(__file__)); RES = os.path.join(HERE, 'results')
def J(n, d=None):
    p = os.path.join(RES, n); return json.load(open(p)) if os.path.exists(p) else d
def JL(n):
    p = os.path.join(RES, n); return [json.loads(l) for l in open(p)] if os.path.exists(p) else []

CORRECTIONS = [
    ('C1', 'PHASE11_STRONGEST_THEOREM (2): doubling rate 16 d C_D^2 / R^2', 'hypothesis R >= 4 C_D omitted', 'add R >= 4 C_D'),
    ('C2', 'PHASE11_STRONGEST_THEOREM (2): Euclidean rate K_D S_c / rho^2', 'rho undefined; K_D needs rho > j_D h / sqrt(2D); pieces are Euclidean balls',
     'rho is the Euclidean partition radius, rho > j_D h / sqrt(2D); for the chair rho = R - 311/175'),
    ('C3', 'PHASE11_STRONGEST_THEOREM (3): lamplighter rate c_k R^(-2/k)', 'the conclusion "not R^-2" needs k >= 2', 'k >= 2'),
    ('C4', 'PHASE11_STRONGEST_THEOREM (4): "every ball contains a based loop with angle >= theta_0"', 'the proof (F2) needs the angle bound on the fundamental loops of a breadth-first tree based at the centre',
     'the hypothesis of the report\'s F2; for finite subgroups of SU(2) in the spinor representation "every r-ball non-flat" suffices'),
    ('C5', 'PHASE11_STRONGEST_THEOREM (5c): "for a finite group, every non-spinor representation\'s floor is a function of the class field"',
     '"non-spinor" is defined for Q8 only; the proof needs 1-dimensional irreducible constituents and plaquettes generating H_1 over Z',
     'representations with only 1-dimensional irreducible constituents, on complexes whose plaquettes generate H_1(.; Z); for Q8 the non-spinor ones'),
    ('C6', 'PHASE11_REPORT, PHASE11_STRONGEST_THEOREM, PHASE12 drafts: printed interval endpoints (e.g. Y6(539311) <= 9.3885937)',
     '88 printed bounds (36 distinct values) rounded to nearest in the wrong direction, by one unit in the last digit; transport bound 1.69927 and share <= 19.7 % rounded the wrong way',
     'every printed bound rounded outward (phase12_rounding_audit.py, test_rounding_outward); no conclusion changes (every comparison using a corrected value keeps a margin >= 2.7e-4); the frozen preregistration file is left unchanged (its context block also gives the L5 gap as 0.0231; the stored rationals give 0.0230244)'),
]

def claims():
    ind = [r for r in JL('phase12_independent.jsonl') if r.get('tag') == 'independent_1387_R20']
    ind_status = ('[C] reproduced' if ind and ind[-1].get('all_balls_certified') else 'failed (see record)' if ind else 'running / not stored')
    law = J('phase12_orbit.json', {}).get('defect_law', {}); pred = J('phase12_predict.json', {})
    ext = J('phase12_extrapolation.json', {}); pr = ext.get('prediction', {})
    y7_status = ('[C] values; prediction ' + ('holds' if pr.get('prediction_holds') else 'falsified')) if 'P1_order' in pr else 'running / not stored'
    verdicts = '; '.join(x['verdict'] for x in ext.get('decision', {}).get('pairs', []) if x['verdict'].startswith('[X]')) or 'none'
    r24 = [r for r in JL('phase12_independent.jsonl') if r.get('tag') == 'prereg_539311_R24']
    part = J('phase12_r24_partial.json', {})
    r24_status = ('[C] passed' if r24 and r24[-1].get('all_balls_certified') else 'failed (see record)' if r24 else
                  f"incomplete: {part['pass2_balls_processed']} of 39117 balls passed, {part['pass2_balls_failed']} failed; not a certificate" if part else 'running / not stored')
    G = ['(G) bounded degree', '(U) unitary connection', '(H) H = D^+D']
    rows = [
        ('XII.A', 'support: E_* = inf over finite legal patches of lambda^D = lim D_R; antitone in the language; frequency-free', '[P]', G, 'report 4.2', 'phase11:test_ladder_finite_radius_obstruction'),
        ('XII.B', 'exact localisation identity (B1) and the two-sided bound Lambda(chi) <= E_* <= D_R, D_R - Lambda <= eps(chi)', '[P]', G + ['(P) partition, c_e > 0'], 'phase12_formal.json:ims_edge_identity', 'test_formal_checks'),
        ('XII.C', 'rates: none from bounded degree or property A; R^-2 from doubling (R >= 4 C_D) or a Euclidean realisation; R^-2 optimal; lamplighter R^(-2/k), k >= 2', '[P]', G, 'report 4.2 table', 'phase11:test_overlap_functions_are_exact'),
        ('XII.N', 'Neumann windows are not compressions and can lie below the floor (pi-flux ladder: 2 - sqrt 2 < 3 - sqrt 5)', '[P]+[C]', G, 'phase11_ladder.json', 'phase11:test_ladder_neumann_windows_saturate_below_floor'),
        ('XII.EN', 'an enumeration of visible environments only can give a false lower certificate (ladder rare seam: 0.49054 claimed, <= 0.40791 true)', '[C]', G, 'phase11_ladder.json:rare', 'phase11:test_ladder_rare_environment_false_certificate'),
        ('XII.OL', 'Orbit Lemma (a)-(e): sigma_{dQ} = rho_Q sigma_d; rho_Q a global gauge transformation; level-1 equivalence; full equivalence and equal E_* on the conjugation stabiliser; otherwise the commutation fails from level 2 (equivalence can fail: 1387 vs 539288)', '[P]', ['Chair44 frame rules', 'Q in S3'],
         'phase12_orbit.json:lemma, phase12_formal.json', 'test_orbit_lemma_records, test_orbit_level1_equal_level2_split_live, test_formal_checks'),
        ('XII.OL.exh', 'exhaustive checks: level-1 spectra constant on all right orbits of the 280 332 representatives (7.8e-14); 912 stabilised pairs equal at level 3 (9.4e-14); exact integer-quaternion link identity', '[C]', [], 'phase12_orbit.json', 'test_orbit_lemma_records'),
        ('XII.closure', 'inside right orbits the exact level-3 coincidences are precisely the closure of conjugation and the stabiliser clause (1612 ties among 1 401 660 pairs, 0 unexplained, 0 explained-but-split); sufficiency proved at all levels', '[P] sufficiency, [C] completeness at level 3, [X] completeness beyond', [], 'phase12_orbit.json:closure', 'test_closure_explains_every_tie'),
        ('XII.FR30', 'E_*(539315) = E_*(FR30): 1386 is fixed by (x y) and 1386.(x y) = 539315 (Orbit Lemma (d))', '[P]', [], 'phase12_orbit.json', 'test_orbit_lemma_stabiliser_clause'),
        ('XII.R20', 'E_*(1387) >= 9.1104981 (R = 20, 24 571 balls, preregistered)', '[C]', ['Higham Thm 10.3, u = 2^-52', 'completeness of the Phi-closure'], 'phase11_cert.jsonl:target_1387_R20', 'test_R20_certificate_record'),
        ('XII.R20.ind', 'the R = 20 certificate reproduced by an implementation sharing no code', ind_status, [], 'phase12_independent.jsonl:independent_1387_R20', 'test_independent_R20_reproduction'),
        ('XII.ind', 'the independent implementation agrees on decoder, links, legal types, exact Y3 and small certificates; it fails where it must', '[C]', [], 'tests', 'test_independent_decoder, test_independent_links_match_phase11, test_independent_small_certificate_and_adversarial'),
        ('XII.F4', 'the maximiser over all 6^8 frame rules is one of 1387, 539311, 1389, 539291', '[C]', ['the funnel X3-X7', 'the R = 20 certificate'], 'phase12_frontier.json', 'test_frontier_table'),
        ('XII.max', '1387 is the global maximiser', 'open (not claimed)', [], 'phase12_frontier.json', 'test_frontier_table'),
        ('XII.break', 'the right-S3 orbit is not a symmetry of the hull operator: E_*(1387) > E_*(539288), 539288 = 4753.(0 2 1)', '[C]', [], 'phase12_orbit.json:lemma.e', 'test_orbit_lemma_records'),
        ('XII.cluster', 'right orbits explain 62 % of the variance of Y3 over all representatives (random blocks: 17 %)', '[E]', [], 'phase12_orbit.json:funnel', 'test_funnel_clustering_record'),
        ('XII.defect', 'the conjugation defect delta_Q(d) controls the splitting (preregistered H1, H2)', '[F]' if law and not law.get('H1_pass') else 'pending', [], 'phase12_orbit.json:defect_law', 'test_defect_law_falsified_as_recorded'),
        ('XII.T31', 'no function of level-one data determines E_* on Chair44 (1387 vs 539288: identical T1 up to gauge, separated floors)', '[P]+[C]', [], 'phase12_orbit.json', 'test_orbit_lemma_records'),
        ('XII.vac', 'on the finite census a finite-radius map exists trivially; level-3 plaquette counts are injective on 1096/1098 classes, so no certified collision exists', '[P]+[C]', [], 'phase10_census.json', 'test_plaquette_counts_almost_injective_on_census'),
        ('XII.T61', 'support-sensitive transport bound E_* >= inf_v alpha(v)/W; Chair44: 1.69926 for the whole orbit of 1387, 1.56874 for FR30 (< 20 % of the floors)', '[P] bound, [C] values', G, 'phase12_transport.json', 'test_transport_bound_records_and_live, test_transport_theorem_on_random_graphs'),
        ('XII.P63', 'no function of cycle lengths, overlaps, eigenangles, plaquette classes and their support is sharp (Z^3 pair: identical inputs, floors separated by 0.18165)', '[P]+[C]', [], 'phase11_z3.json:audit', 'phase11:test_z3_pair_audit'),
        ('XII.int', 'single-child interventions do not change Lambda_R monotonically: around FR30 2 of 22 neighbours raise Lambda_6 and 20 lower it; around 4753 all 38 non-trivial neighbours lower it', '[E]', ['float Lambda_R at R = 6, 8'], 'phase12_intervention.jsonl', 'test_intervention_both_signs'),
        ('XII.int.P51', 'language inclusion (Theorem A2) implies Lambda_R, D_R and E_* do not decrease; its radius-1 hypothesis fails for all 60 non-trivial neighbours; each intervention changes the link on 27-74 % of the panels of T_2..T_4', '[P] + [C]', [], 'phase12_intervention_analysis.json', 'test_intervention_analysis'),
        ('XII.int.U1', 'sign Delta(6) = sign dU1 = sign dD(6) = sign dY5 on all 61 neighbours; signs persist from R = 6 to 8 on the 7 computed', '[E]', ['float eigenvalues', 'two neighbourhoods'], 'phase12_intervention_analysis.json', 'test_intervention_analysis'),
        ('XII.cube.OL', 'cube family: the Orbit Lemma transfers (level-1 equivalence for all 48 Q at theta = pi/2; at theta = pi/5 for the 24 proper Q only; broken from level 2)', '[P]+[E]', ['Cube48, theta-connections'], 'phase12_cube.json:orbit', 'test_cube_orbit_lemma_transfers'),
        ('XII.cube.rep', 'cube family: the order of spinor and adjoint floors flips with theta (adjoint below at pi/2, above at pi/5)', '[E]', [], 'phase12_cube.json:orbit', 'test_cube_representation_order_flips'),
        ('XII.cube.flat', 'cube family: the identity rule is flat, E_* = 0 (pinned T_L bottoms equal the trivial Dirichlet values)', '[P]', [], 'phase12_cube.json:flat_identity_rule', 'test_cube_flat_rule'),
        ('XII.pred', 'preregistered predictive study (frozen split, target Y5): results per descriptor family' + (f" (best test Spearman {max(r['spearman_test'] for r in pred['families'].values()):.3f})" if pred else ''), '[E]' if pred else 'pending', [], 'phase12_predict.json', 'test_prediction_preregistered_before_targets, test_prediction_results'),
        ('XII.y7', 'the frozen level-7 prediction (P1 order 539311 > 1387 > 539291 > 1389, P2 gap in [0.010, 0.030]) scored on exact rational Y7 of the four frontier rules', y7_status, ['pinned T7, 2 097 152 tiles'], 'phase12_y7.jsonl, phase12_extrapolation.json:prediction', 'test_y7_records, test_extrapolation_results'),
        ('XII.y7.method', 'the lean level-L assembly is Phase XI operator entry for entry; the checkpointed Lanczos agrees with ARPACK and resumes exactly', '[C]', [], 'audit/phase12_y7.py', 'test_y7_operator_identical_to_phase11, test_lanczos_matches_arpack_and_resumes'),
        ('XII.r24', 'preregistered radius-24 certificate: E_*(539311) >= mu - (Higham term) > Y7(1389) = 9.2083453, mu = 9655658/2^20, so 1389 is not the maximiser', r24_status,
         ['Higham Thm 10.3, u = 2^-52', 'completeness of the Phi-closure'], 'phase12_independent.jsonl:prereg_539311_R24, phase12_preregistration_r24.json', 'test_r24_protocol_frozen, test_r24_certificate'),
        ('XII.extrap', 'two-sided extrapolation of the frontier floors (frozen protocol, 2b450cc): ' + verdicts, '[X]' if ext else 'running / not stored', ['model Y_L = E + A q^L', 'model Lambda_R = E - C / rho^2'], 'phase12_extrapolation.json:decision', 'test_extrapolation_protocol_frozen, test_extrapolation_results'),
        ('XII.ug.P151', 'Proposition 15.1: for every Q8 gauge section s of a patch K, lambda_min(P_K H P_K) <= B(s) = [sum_e (2 - 2 Re d_e) + b(K)] / |K|', '[P]', ['quaternion form of the spinor operator'], 'report 15', 'test_unique_games_proposition_15_1'),
        ('XII.ug.E', 'Chair44 rules as Q8 unique games: best sections found satisfy 44.9-50.2 % of panels; frustration ranks the rules only loosely like the floor (Spearman 0.70-0.78)', '[E] heuristic', ['spectral rounding + local search'], 'phase12_unique_games.jsonl', 'test_unique_games_proposition_15_1'),
        ('XII.ugt', 'the claimed Unique Games Theorem and Min-UnCut hardness (openai/math, 23 Sep 2026; not checked here) are worst-case statements on finite instances and do not bound, order or certify any Chair44 floor', '[P] (scope)', ['claims external, unverified'], 'report 15', '-'),
        ('XII.lean', 'Lean formalisation', 'not done: toolchain hosts denied by the environment network policy', [], 'phase12_formal.json:lean', '-'),
        ('XII.phys', 'a physical law, observable or discovery', 'not claimed', [], '-', '-'),
    ]
    return [dict(zip(('id', 'claim', 'status', 'assumptions', 'evidence', 'test'), r)) for r in rows]

if __name__ == '__main__':
    findings = [{'id': 'IF1', 'where': 'audit/phase11_chair.py banded_cert (and the first version of phase12_independent.higham)',
                 'finding': 'the assertion (d - mu) + mu == d in floating point does not prove that the diagonal shift d - mu was exact (24 - 0.1 passes it)',
                 'impact': 'none on stored results: every stored certificate uses a dyadic mu = k / 2^20 (or 2^30), for which 24 - mu is exact; checked by test_stored_certificate_shifts_exact',
                 'fix': 'phase12_independent now compares in rational arithmetic; Phase XI code left unchanged (frozen artifact)'}]
    out = {'implementation_findings': findings, 'commit': subprocess.run(['git', 'rev-parse', '--short', 'HEAD'], capture_output=True, text=True, cwd=HERE).stdout.strip(),
           'report': 'deliverables/PHASE12_REPORT.md', 'claims': claims(),
           'corrections': [dict(zip(('id', 'statement', 'problem', 'correction'), c)) for c in CORRECTIONS]}
    json.dump(out, open(os.path.join(RES, 'phase12_ledger.json'), 'w'), indent=1)
    print(len(out['claims']), 'claims;', len(out['corrections']), 'corrections')
