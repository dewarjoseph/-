#!/usr/bin/env python3
"""Phase XI: the reconciled Phase X proof-obligation table and the Phase XI claims ledger.

Reads the committed artifacts of Phases X and XI and writes audit/results/phase11_ledger.json:
  proof_obligations  every Phase X claim decomposed into obligations; each with its nature (proof / exact arithmetic /
                     floating point with a rounding bound / floating point evidence / artifact only) and how Phase XI discharged it
  bound_types        each numerical bound used in a comparison, with its certificate type
  reconciliation     the R = 14 / R = 15 certificates of class 1387
  claims             Phase XI claims with status labels [P] proved, [C] computer-certified, [E] floating-point evidence, [X] conjecture,
                     [F] falsified, and the test that checks each
Usage: python -u -I audit/phase11_ledger.py"""
import os, sys, json, subprocess
from fractions import Fraction
HERE = os.path.dirname(os.path.abspath(__file__)); RES = os.path.join(HERE, 'results')
def J(name, default=None):
    p = os.path.join(RES, name)
    return json.load(open(p)) if os.path.exists(p) else default
def JL(name):
    p = os.path.join(RES, name)
    return [json.loads(l) for l in open(p)] if os.path.exists(p) else []

def certs():
    out = {}
    for r in JL('phase11_cert.jsonl'):
        if r.get('tag', '') and r['tag'].startswith(('audit_', 'target_')): out[r['tag']] = r
    return out

def main():
    C = certs(); p10 = {(str(r.get('class', r.get('extended_index'))), r['R']): r for r in JL('phase10_ims.jsonl')}
    rec = lambda tag: C.get(tag, {})
    def cert_row(tag, p10key):
        a = rec(tag); b = p10.get(p10key, {})
        return {'phase10_value': b.get('Lambda_R_certified'), 'phase10_balls': b.get('distinct_balls'), 'phase11_value': a.get('Lambda_R_certified'),
                'phase11_balls': a.get('distinct_balls'), 'phase11_all_certified': a.get('all_balls_certified'), 'phase11_rejected': a.get('rejected_incomplete'),
                'mu': a.get('mu'), 'independent_implementation': a.get('implementation')}
    reconciliation = {
        '1387_R14': cert_row('audit_1387_R14', ('1387', 14)), '1387_R15': cert_row('audit_1387_R15', ('1387', 15)),
        'twin539311_R14': cert_row('audit_twin_R14', ('539311', 14)), 'FR30_R12': {'phase7_value': 7.954292264597248, **cert_row('audit_FR30_R12', ('4752', 12))},
        'statement': ('The Phase X report cites both certificates; its ledger (written at 529bba9) and tests stopped at R = 14. Both are now '
                      'independently re-certified (own enumeration, own completeness test, symbolic derivation of the overlap function, banded '
                      'Higham certificates). The ledger and tests use the R = 15 value. With R = 15 the comparison E_*(1387) > E_*(FR30) no longer '
                      'needs the Phase VIII bound 8.7642270 (a 1.77M-dimensional eigenvector that is not stored): the exact level-5 bound '
                      'Y_5(FR30) = 8.797011 < 8.7999987 suffices, and it is recomputed independently in Phase XI.')}
    proofs = J('phase11_proofs.json', {})
    y6 = {r['j']: r for r in JL('phase11_orbit_Y6.jsonl')}; p10y6 = {}
    cls_j = {1387: 184323, 1389: 184338, 1391: 184342}
    for r in JL('phase10_deep.jsonl'):
        if r.get('class') in cls_j and r.get('Y6_upper'): p10y6[cls_j[r['class']]] = r['Y6_upper']
    for r in JL('phase10_improper_certify.jsonl'):
        if r.get('Y6_upper'): p10y6[r['j']] = r['Y6_upper']
    y6_note = '; '.join(f"{j}: {y6[j]['upper']:.10f}" + (f" vs Phase X {p10y6[j]:.10f}" if j in p10y6 else ' (new)') for j in sorted(y6)) or 'pending'
    ch = J('phase11_fr30_upper.json', {}).get('chain', [])
    fr30_note = '; '.join(f"U{r['m']} = {r['upper']:.10f} ({r['upper_exact']})" for r in ch) or 'pending'
    cen = J('phase11_frontier_census.json', {}).get('rows', [])
    census_note = ('independent recomputation of the free-T3 Higham bound and exact Y4 for all %d classes: min certified F3 = %.7f; %d classes with exact Y4 < 7.954291 (Phase X: 806)'
                   % (len(cen), min(r['F3_certified'] for r in cen), sum(Fraction(int(r['Y4_num']), int(r['Y4_den'])) < Fraction(7954291, 10 ** 6) for r in cen))) if cen else 'pending'
    z3 = J('phase11_z3.json', {})
    obligations = [
        ('O1', 'Pauli links lie in Q8; reverse crossing gives the inverse; the sign of the normal is irrelevant', 'proof',
         'algebra: (sigma.u)^2 = 1 for a unit vector u; independent implementation agrees entrywise on T_3 of 4752, 1387, 937', 'discharged'),
        ('O2', 'Deg = 24 on every chair tiling, so H_Y = 24 - A_U = D_U^+ D_U', 'proof',
         f"the chair has {proofs.get('panels', {}).get('boundary_faces', 24)} unit boundary faces; each is shared with exactly one tile in a tiling of R^3", 'discharged'),
        ('O3', 'pinned operator on a legal patch = compression of H_Y, hence lambda_min >= E_*', 'proof', 'variational principle; legality gives occurrence (minimality) or the language definition of E_*', 'discharged'),
        ('O4', 'exact rational Rayleigh quotients are rigorous upper bounds', 'exact arithmetic',
         'recomputed independently for Y3 (all 280 332 extended orbit representatives), Y4 (all survivors), Y5 (top-40 classes and twins, counterfactuals), '
         'Y6 of the six orbit members (%s) and of 515963' % y6_note, 'discharged for L <= 5 and for the orbit at L = 6'),
        ('O5', 'free supertile bottom F_k is a lower bound on E_* (Theorem X.2)', 'proof',
         'every hull tiling is sigma^k of a hull tiling (compactness), hence partitioned into level-k supertiles; links are invariant under global proper or improper frames; dropping inter-supertile panels lowers the form', 'discharged'),
        ('O6', 'IMS identity with amplified links (Phase VII Thm 7.1, X.7)', 'proof', 'Theorem XI.B1 (exact identity); randomized identity test max error %s' % proofs.get('ims_random', {}).get('max_identity_error'), 'discharged'),
        ('O7', 'c(eta) is the overlap of the 3D Dirichlet ground state', 'proof (symbolic)', 'phase11_proofs.overlap3d: equals the Phase VII closed form: %s' % proofs.get('overlap3d', {}).get('equals_phase7_formula'), 'discharged'),
        ('O8', 'r_c = sqrt(619)/14 <= 311/175', 'exact', 'phase11_proofs.rc: (311/175)^2 - r_c^2 = %s > 0' % proofs.get('rc', {}).get('bound_311_175_squared_minus_rc_squared'), 'discharged'),
        ('O9', 'the Phi-closure of the T5 1-star types is the set of all legal 1-star types', 'proof + per-instance checks',
         'closure lemma asserted on every Phi step; frame substitution irreducible (Cayley digraph of the generated finite group); independent closure gives identical key sets for 4752, 1387, 1389, 1391', 'discharged'),
        ('O10', 'every enumerated R-ball is complete (no tile of any tiling containing the patch is missing)', 'exact geometric check',
         'independent criterion: nearest unowned cube centre at distance >= R + sqrt(3)/2; 0 rejections at R = 8, 12, 14, 15', 'discharged'),
        ('O11', 'Higham Cholesky certificate (Thm 10.3) implemented soundly', 'floating point with rounding bound',
         'independent path: RCM + banded LAPACK dpbtrf, u = 2^-52, Frobenius sum inflated by (1 + 2Ku); the GPU path used dense cuSOLVER with u = 2^-51', 'discharged'),
        ('O12', 'amplification factors rounded to double', 'rounding bound', 'evaluated at 60 digits; entry error 24 * max amp * 2^-52 subtracted', 'discharged'),
        ('O13', 'the localisation certificates of table 1.1: E_*(1387) >= 8.7999988 (R = 15) and >= 8.7644994 (R = 14), E_*(FR30) >= 7.954292 (Phase VII, R = 12), twin >= 8.7644994 (R = 14)', 'certificate',
         'independently re-certified: ' + json.dumps({k: {kk: reconciliation[k][kk] for kk in ('phase11_value', 'phase11_balls', 'phase11_all_certified')} for k in ('1387_R15', '1387_R14', 'FR30_R12', 'twin539311_R14')}), 'discharged'),
        ('O14', 'E_*(FR30) <= 8.7642270381 (Phase VIII sigma^5 of type 59, 884 736 tiles)', 'exact rational of an unstored vector',
         'reproduced independently by phase11_fr30_upper (sigma^5 of the minimising self-loop type): %s' % fr30_note, 'discharged (independent value 5e-9 higher)'),
        ('O15', 'the mirror twin 539311 has a higher floor than FR30', 'certificate + upper bound',
         'Phase X used the Phase VIII bound (artifact) against the R = 14 twin certificate. Phase XI: twin R = 15 certificate %s > Y5(FR30) = 8.7970113 (independent exact)' % (rec('target_twin_R15').get('Lambda_R_certified'),), 'discharged without artifacts'),
        ('O16', 'Z^3 class-field-matched pair (X.5): identical classes, gauge-equivalent shadows, separation >= 0.18', 'exact + certificate',
         'independent rebuild: %s' % json.dumps({k: z3.get('audit', {}).get('class_matched', {}).get(k) for k in ('class_fields_identical', 'shadow_ratio_flat', 'certified_separation')}), 'discharged'),
        ('O17', 'Z^3 trace-matched pair: two shadows certified above the non-Abelian floor', 'floating point with heuristic margin',
         'Phase X used a Lipschitz branch and bound on float eigenvalues with margin 1.2e-9: evidence, not a strict certificate; see Phase XI z3 shadow free-cell bounds', 'reclassified [E]'),
        ('O18', 'census: every class has E_* >= 3.788; 806 classes rigorously below FR30 (Phase X, Y4 alone)', 'certificates', census_note, 'discharged'),
        ('O19', 'primitivity of every proper rule; period 2 for the twins', 'exact',
         'recomputed independently (frame substitution digraph, boolean closure); an integer-overflow bug in Phase XI\'s own flag was found and fixed; the certificate does not use the flag', 'discharged'),
        ('O20', 'periodic-approximant floors (Phase X section 9 row 11)', 'floating point evidence', 'Bloch minima are float; stated as evidence', 'unchanged [E]'),
    ]
    out = {'commit': subprocess.run(['git', 'rev-parse', '--short', 'HEAD'], capture_output=True, text=True, cwd=HERE).stdout.strip(),
           'report': 'deliverables/PHASE11_REPORT.md', 'reconciliation': reconciliation,
           'proof_obligations': [dict(zip(('id', 'obligation', 'nature', 'how', 'status'), o)) for o in obligations]}
    out['claims'] = claims(C)
    extra = J('phase11_ledger_claims.json', {})
    out.update(extra)
    json.dump(out, open(os.path.join(RES, 'phase11_ledger.json'), 'w'), indent=1, default=float)
    print(json.dumps(reconciliation, indent=1, default=float)[:3000])

def claims(Cr):
    """the Phase XI claims: label ([P] proved, [C] computer-certified, [E] evidence, [X] conjecture, [F] falsified), where it is
    stated, the artifact that carries it, and the test that re-checks it"""
    t1391 = Cr.get('target_1391_R18', {}); lb = J('phase11_leaderboard.json', {}); orb = lb.get('orbit_1387', {})
    rows = [
        ('XI.A', 'E_* = lim D_R over legal environments; antitone in the language; frequency-free (bounded degree only)', '[P]', '§3', '-', '-'),
        ('XI.B', 'exact IMS identity with amplified links; Lambda <= E_* <= D', '[P]', '§3', 'phase11_proofs.json:ims_random', 'test_ims_identity_and_lower_bound_random'),
        ('XI.C', 'uniform localisation <=> property A; O(R^-2) with explicit constants (doubling, Euclidean); R^-2 optimal; lamplighter R^(-2/k)', '[P]', '§3', 'phase11_proofs.json', 'test_overlap_functions_are_exact, test_rc_panels_q8'),
        ('XI.C/N', 'Neumann windows converge to the wrong limit (pi-flux ladder: 2 - sqrt 2 < 3 - sqrt 5)', '[P]+[C]', '§3, §6', 'phase11_ladder.json', 'test_ladder_neumann_windows_saturate_below_floor'),
        ('XI.D', 'Phi-closed enumeration is complete; a visible-only enumeration gives a false certificate', '[P]+[C]', '§3, §6', 'phase11_ladder.json:rare', 'test_ladder_rare_environment_false_certificate'),
        ('XI.E', 'cycle-cover bound; Z^3 without trivial Q8 plaquettes has E_* >= 6(1 - cos(pi/8))', '[P]', '§4', 'phase11_z3.json:cover', 'test_z3_no_trivial_plaquette_bound, test_cycle_laplacian_formula'),
        ('XI.F', 'loop-transport and flatness-radius bounds; E_* > 0 <=> finite flatness radius under the angle gap', '[P]', '§4', 'phase11_proofs.json:transport', 'test_loop_transport_bound_random'),
        ('XI.G', 'no lower-semicontinuous frequency functional bounds E_*', '[P]', '§4', 'phase11_z3.json:islands', 'test_z3_islands'),
        ('XI.H3', 'non-spinor floors are functions of the plaquette class field; X.5 lives in the spinor component', '[P]', '§4', 'phase11_z3.json:audit', 'test_z3_pair_audit'),
        ('XI.I', 'no fixed radius determines E_*; the profile has no closed recursion', '[P]+[C]', '§4, §7', 'phase11_ladder.json:finite_radius, profile_no_recursion', 'test_ladder_finite_radius_obstruction'),
        ('VI.1', 'class-field insufficiency on the ladder (certified separation 0.297)', '[C]', '§6', 'phase11_ladder.json:insufficiency', 'test_ladder_insufficiency'),
        ('VI.2', 'non-minimal hull: E_* not constant without minimality', '[C]', '§6', 'phase11_ladder.json:nonminimal', 'test_ladder_nonminimal'),
        ('I.1', 'independent re-certification: FR30 R = 12, 1387 R = 14 and 15, twin R = 14', '[C]', '§1', 'phase11_cert.jsonl', 'test_independent_recertification'),
        ('I.2', 'E_*(1387) > E_*(FR30) without stored-only artifacts (separation >= 0.0029876)', '[C]', '§1', 'phase11_cert.jsonl, phase11_frontier_counterfactual_Y5.jsonl', 'test_1387_above_fr30_without_phase8'),
        ('I.3', 'the Phase X Z^3 trace-pair shadow bound is evidence, not a certificate', '[E] (reclassified)', '§1', '-', '-'),
        ('II.1', 'E_*(539311) >= 8.7999990 (R = 15, 10 321 balls)', '[C]', '§2.2', 'phase11_cert.jsonl:target_twin_R15', 'test_new_certificates'),
        ('II.2', 'E_*(1389) >= 8.7644993 (R = 16) > 8.7642271 >= E_*(FR30) (independent U5): no artifacts', '[C]', '§2.1', 'phase11_cert.jsonl, phase11_fr30_upper.json', 'test_new_certificates, test_1389_above_fr30_without_artifacts'),
        ('II.3', 'E_*(1391) >= 8.7645 (R = 18, preregistered)', ('[C]' if t1391.get('all_balls_certified') else 'failed at mu (see record)' if t1391 else 'not completed'), '§2.1',
         'phase11_cert.jsonl:target_1391_R18', 'test_new_certificates' if t1391.get('all_balls_certified') else '-'),
        ('II.4', 'the proper-rule maximiser is one of 1387, 1389, 1391 (1095 classes proven inferior)', '[C]', '§2.1', 'phase11_leaderboard.json', 'test_leaderboard_classification'),
        ('II.5', 'the maximiser over all 6^8 frame rules lies in the right-S3 orbit of 1387 (exhaustive funnel X3-X7)', '[C]', '§2.2',
         'phase11_frontier_*.jsonl, phase11_frontier_summary.json', 'test_funnel_flags_recomputed_from_stored_rationals, test_orbit_reps_cover_the_extended_space, test_right_S3_orbit_of_1387'),
        ('II.6', 'which orbit member is maximal: open (%s)' % ('resolved' if orb.get('resolved') else 'all six intervals overlap'), 'open', '§2.4', 'phase11_leaderboard.json:orbit_1387', 'test_leaderboard_classification'),
        ('II.7', 'E_*(539315) = E_*(FR30) (FR30 mirror via 1386)', '[P]+[C]', '§2.3', 'phase11_mechanism.json:twins_by_member', 'test_fr30_mirror_has_fr30_types'),
        ('II.8', '"the mirror twin of a class" is ill-defined (member-dependent)', '[P] (correction of Phase X)', '§2.3', 'phase11_mechanism.json:twin_triples', '-'),
        ('II.9', 'twin criterion: sign dU1 predicts sign dY5 in 31/40 (preregistered)', '[E] correlation', '§2.3', 'phase11_analysis.json:twins', 'test_preregistered_evaluations'),
        ('II.10', 'probes: Lambda_R(1387) <= 9.1675 at R <= 22 (sampled legal balls; float Rayleigh quotients)', '[E]', '§2.4', 'phase11_probe_*.json', '-'),
        ('V.1', 'P1-P3 pass on the single-child neighbourhoods (preregistered)', '[E] preregistered', '§5', 'phase11_analysis.json:counterfactual', 'test_preregistered_evaluations'),
        ('V.2', '1387 is a local maximum of Y5 under single-child changes (one tie: a neighbour in its own orbit)', '[C] at level 5', '§5', 'phase11_analysis.json:counterfactual', 'test_preregistered_evaluations'),
        ('V.3', 'FR30 -> 4753 raises the worst local energy on all 16 geometric 1-star configurations and removes the three two-cycle-flat types', '[C] at radius 1', '§5', 'phase11_mechanism.json', 'test_mechanism_every_shape_raised'),
        ('V.4', 'two-cycle-flat tiles are associated with lower floors (random sample, p = 4e-11)', '[E] post hoc', '§5', 'phase11_analysis.json:census_bounds.random200', 'test_random_sample_association'),
        ('VII.1', 'the certified local frustration profile separates the Z^3 pair at R = 5 and not 937/938', '[C]', '§7', 'phase11_z3.json:profile', 'test_z3_profile_separates_the_pair'),
        ('XII.1', 'Chair44 edge exponent > 2', '[X]', '§12', '-', '-'),
        ('VIII.1', 'a physical law, quantum dynamics or particle spectrum follows', 'not claimed', '§8', '-', '-'),
    ]
    return [dict(zip(('id', 'claim', 'status', 'where', 'artifact', 'test'), r)) for r in rows]

if __name__ == '__main__': main()
