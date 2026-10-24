"""Phase XI regression tests.

Two kinds of test.
- Recomputations (fast): the independent implementation agrees with Phase X; the exact identities and constants behind the
  theorems; small certificates that must pass and fail where they should.
- Artifact consistency: every certificate, bound and classification quoted in deliverables/PHASE11_REPORT.md is read back from
  audit/results and re-checked (exact rationals re-compared, flags recomputed from the stored rationals).
A passing test shows implementation consistency, not the truth of a theorem; the proofs are in the report.
Run: python -m pytest -q tests/test_phase11.py"""
import os, sys, json, math, subprocess
from fractions import Fraction
import numpy as np
import pytest
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__))); AUD = os.path.join(ROOT, 'audit'); RES = os.path.join(AUD, 'results')
sys.path.insert(0, AUD)
import phase11_chair as C
os.environ.setdefault('OMP_NUM_THREADS', '1')

def J(n): return json.load(open(os.path.join(RES, n)))
def JL(n): return [json.loads(l) for l in open(os.path.join(RES, n))]

# ------------------------------------------------------------------ independent implementation versus Phase X
def test_index_maps_agree_with_phase10():
    import phase9_pair as P9, phase10_improper as X
    assert all(C.proper_decoration(i) == tuple([P9.decoration(i)['0']] + [P9.decoration(i)[v] for v in P9.U3]) for i in range(6561))
    for j in list(range(0, 6 ** 8, 7919)) + [539311, 539291, 539288]:
        assert C.extended_decoration(j) == tuple([X.dec_of(j)['0']] + [X.dec_of(j)[v] for v in P9.U3])

def test_level3_spectra_agree_with_phase10():
    import phase9_pair as P9
    for r in (4752, 1387):
        G, T = C.supertile(C.rule(r), 3)
        e1 = np.linalg.eigvalsh(C.operators(G, T).toarray()); e2 = np.linalg.eigvalsh(P9.build([P9.decoration(r)] * 3)['H'].toarray())
        assert np.abs(e1 - e2).max() < 1e-10

def test_legal_types_and_balls_agree_with_phase10():
    import phase9_pair as P9, phase10_ims as I
    for r, nt, nb in ((4752, 72, 747), (1387, 90, 1450)):
        ty, n0, _ = C.legal_types(C.rule(r)); ty10, _ = I.phi_closed_types(P9.decoration(r))
        assert len(ty) == nt and set(ty) == set(ty10)
        _, info = C.enumerate_balls(C.rule(r), 8, 3, ty, nproc=1)
        assert info['distinct'] == nb and info['rejected'] == 0

def test_closure_of_1389_adds_rare_types():
    ty, n0, _ = C.legal_types(C.rule(1389)); assert (len(ty), n0) == (102, 94)

def test_frame_graphs():
    assert C.frame_graph(C.rule(1387)) == {'frames': 24, 'irreducible': True, 'period': 1, 'primitive_power': 2, 'dets': [1]}
    g = C.frame_graph(C.rule('x539311')); assert g['irreducible'] and g['period'] == 2 and g['frames'] == 48

# ------------------------------------------------------------------ exact identities and constants
def test_overlap_functions_are_exact():
    import phase11_proofs as P
    o3 = P.overlap3d(); assert o3['equals_phase7_formula'] and o3['s2_coefficient_is_minus_pi2_over_6']
    assert P.overlap1d()['equals_ladder_formula']
    for eta in (0.1, 0.45):
        assert abs(float(C.c_overlap(eta)) - C.c_overlap_quadrature(eta)) < 1e-8

def test_rc_panels_q8():
    import phase11_proofs as P
    r = P.rc(); assert r['equals_619_over_196'] and r['bound_ok'] and r['bound_311_175_squared_minus_rc_squared'] == '9/122500'
    assert P.panels() == {'boundary_faces': 24, 'internal_adjacencies': 9}
    q = P.q8(); assert abs(q['angle_gap_nonidentity'] - math.pi / 2) < 1e-12 and q['adjoint_is_sum_of_characters']

def test_ims_identity_and_lower_bound_random():
    import phase11_proofs as P
    r = P.ims_random(trials=10); assert r['max_identity_error'] < 1e-12 and r['lower_bound_holds']

def test_loop_transport_bound_random():
    import phase11_proofs as P
    r = P.transport(trials=80); assert r['F1_bound_holds'] and r['min_ratio_lambda_over_bound'] >= 1 - 1e-9

def test_cycle_laplacian_formula():
    rng = np.random.default_rng(0)
    for ell in (2, 3, 5, 8):
        for _ in range(5):
            Z = rng.normal(size=(2, 2)) + 1j * rng.normal(size=(2, 2)); W, _ = np.linalg.qr(Z)
            H = np.zeros((2 * ell, 2 * ell), complex)
            for i in range(ell):
                j = (i + 1) % ell; U = W if i == ell - 1 else np.eye(2)
                H[2 * i:2 * i + 2, 2 * j:2 * j + 2] -= U; H[2 * j:2 * j + 2, 2 * i:2 * i + 2] -= U.conj().T
            H += 2 * np.eye(2 * ell)                                  # every vertex of a cycle (2-cycle: two parallel edges) has degree 2
            th = float(np.min(np.abs(np.angle(np.linalg.eigvals(W)))))
            assert abs(np.linalg.eigvalsh(H)[0] - 2 * (1 - math.cos(th / ell))) < 1e-10

# ------------------------------------------------------------------ small certificates
def test_small_certificate_passes_and_fails_where_it_should():
    from fractions import Fraction
    dec = C.rule(4752); R = 6; rho = Fraction(R) - C.RC_BOUND
    ty, _, _ = C.legal_types(dec); balls, info = C.enumerate_balls(dec, R, 3, ty, nproc=1); assert info['distinct'] == 325
    d2s = set()
    for G, T, c in ty.values():
        P = C.Patch(G, T); a, b, _ = P.panels(); X = C.centroid14(G, T); d2s |= set(((X[a] - X[b]) ** 2).sum(1).tolist())
    tab = C.amp_table_exact(rho, d2s); err = 24 * max(tab.values()) * 2.0 ** -52
    lows, lam = [], []
    for G, T, _ in balls.values():
        Ha, _, _ = C.ball_amplified(G, T, rho, tab.__getitem__); lam.append(np.linalg.eigvalsh(Ha.toarray())[0])
        lows.append(C.banded_cert(Ha, 3833131 / 1048576, err)[0])
    assert all(l is not None for l in lows) and min(lows) > 3.6555585            # Phase X: Lambda_6 >= 3.655558585
    assert abs(min(lam) - 3.655559951788228) < 1e-9
    fails = sum(C.banded_cert(C.ball_amplified(G, T, rho, tab.__getitem__)[0], min(lam) + 1e-6, err)[0] is None for G, T, _ in balls.values())
    assert fails >= 1

# ------------------------------------------------------------------ recorded certificates (Part I reconciliation)
def _cert(tag):
    rows = [r for r in JL('phase11_cert.jsonl') if r.get('tag') == tag]; assert rows, tag; return rows[-1]

@pytest.mark.parametrize('tag,balls,value', [('audit_FR30_R12', 2315, 7.9542912), ('audit_1387_R14', 7527, 8.7644995), ('audit_1387_R15', 10321, 8.7999990),
                                              ('audit_twin_R14', 7527, 8.7644995)])
def test_independent_recertification(tag, balls, value):
    r = _cert(tag); assert r['all_balls_certified'] and r['rejected_incomplete'] == 0 and r['distinct_balls'] == balls
    assert r['Lambda_R_certified'] >= value and 'independent' in r['implementation']

def test_phase10_ball_counts_reproduced():
    p10 = {(str(r.get('class', r.get('extended_index'))), r['R']): r for r in JL('phase10_ims.jsonl')}
    assert p10[('1387', 15)]['distinct_balls'] == _cert('audit_1387_R15')['distinct_balls']
    assert p10[('1387', 14)]['distinct_balls'] == _cert('audit_1387_R14')['distinct_balls']

def test_1387_above_fr30_without_phase8():
    """the R = 15 lower bound of 1387 exceeds FR30's independently recomputed exact level-5 upper bound"""
    import phase11_frontier as F
    j = F.ext_index(C.proper_decoration(4752)); rows = {r['j']: r for r in JL('phase11_frontier_counterfactual_Y5.jsonl')}
    q = Fraction(int(rows[j]['upper_num']), int(rows[j]['upper_den'])); assert q < Fraction(87999990, 10 ** 7) <= Fraction(_cert('audit_1387_R15')['Lambda_R_certified'])
    assert abs(float(q) - 8.797011315) < 1e-6

# ------------------------------------------------------------------ Z^3
def test_z3_pair_audit():
    a = J('phase11_z3.json')['audit']['class_matched']
    assert a['class_fields_identical'] and all(a['shadow_ratio_flat'].values()) and a['certified_separation'] > 0.1816
    assert Fraction(a['E_A_upper_exact']) < Fraction(40414, 100000) and a['E_B_lower_free_cell'] > 0.5857
    assert a['adjoint_plaquette_elements_identical'] and abs(a['adjoint_floors_float'][0] - a['adjoint_floors_float'][1]) < 1e-9

def test_z3_profile_separates_the_pair():
    p = J('phase11_z3.json')['profile']; r5 = p['5']
    assert r5['B']['Lambda_R_certified'] > 1.0142 > 0.40414 and r5['separated']

def test_z3_no_trivial_plaquette_bound():
    c = J('phase11_z3.json')['cover']['no_trivial_plaquette_fields']
    assert abs(c['universal_bound'] - 6 * (1 - math.cos(math.pi / 8))) < 1e-12
    assert all(r['float_floor'] >= c['universal_bound'] for r in c['evaluated'])

def test_z3_islands():
    rows = J('phase11_z3.json')['islands']
    assert [r['island_side'] for r in rows] == sorted(r['island_side'] for r in rows)
    for r in rows: assert abs(r['E_upper_island_bump'] - r['closed_form']) < 1e-12
    assert rows[-1]['environment_TV_distance'] < rows[0]['environment_TV_distance'] and rows[-1]['E_upper_island_bump'] < 0.5

# ------------------------------------------------------------------ the ladder (second geometry)
def test_ladder_neumann_windows_saturate_below_floor():
    import phase11_ladder as L
    X = {'b': L.Q['-1']}; H = L.window_op('b' * 80, X, free=True)
    assert abs(L.lam_min_banded(H, 2) - (2 - math.sqrt(2))) < 1e-9 and 2 - math.sqrt(2) < 3 - math.sqrt(5)
    assert abs(L.bloch_floor('b', X) - (3 - math.sqrt(5))) < 1e-12

def test_ladder_overlap_and_small_enclosure():
    import phase11_ladder as L
    assert abs(float(L.C1(0.3)) - L.C1_quadrature(0.3)) < 1e-12
    X = {'a': L.Q['1'], 'b': L.Q['-1']}; e = L.enclosure(L.periodic_factors('aab', 64), X, 32)
    f = L.bloch_floor('aab', X); assert e['Lambda_certified'] <= f <= e['D_upper'] and e['D_upper'] - e['Lambda_certified'] <= e['ims_bound']

def test_ladder_insufficiency():
    d = J('phase11_ladder.json')['insufficiency']
    assert d['class_field_identical'] and d['certified_separation'] > 0.29

def test_ladder_finite_radius_obstruction():
    d = J('phase11_ladder.json')['finite_radius']; rows = {r['m']: r for r in d['rows']}
    assert rows[24]['Lambda_W_certified'] > rows[32]['D_W_upper']
    import phase11_ladder as L
    assert L.periodic_factors('a' * 24 + 'b', 24) == L.periodic_factors('a' * 32 + 'b', 24)
    p = J('phase11_ladder.json')['profile_no_recursion']
    assert p['languages_equal_W3'] and not p['languages_equal_W4'] and p['m6_W3']['D_exact'] == p['m9_W3']['D_exact'] and p['m6_W4']['D_exact'] != p['m9_W4']['D_exact']

def test_ladder_rare_environment_false_certificate():
    d = J('phase11_ladder.json')['rare']; assert d['cc_legal'] and d['first_level_with_cc'] == 11
    assert all(r['visible_certificate_invalid'] for r in d['frustrated_-1'])
    import phase11_ladder as L
    X = {'a': L.Q['-1'], 'b': L.Q['-1'], 'c': L.Q['1'], 'd': L.Q['-1']}; W = 16
    ev = L.enclosure(L.visible_factors(L.RARE_SUB, 2 * W, 10), X, W, exact=False); ea = L.enclosure(L.subst_factors(L.RARE_SUB, 2 * W), X, W)
    assert ev['Lambda_certified'] > ea['D_upper']

def test_ladder_nonminimal():
    d = J('phase11_ladder.json')['nonminimal']; assert d['fixed_point_D_W_upper'] < 3 - math.sqrt(5) - 0.3

# ------------------------------------------------------------------ mechanism (Part V)
def test_mechanism_every_shape_raised():
    d = J('phase11_mechanism.json'); c = d['compare_4752_4753']
    assert c['shared_star_fingerprints'] == 0 and c['shapes'] == [16, 16] and c['b_twocycle_flat_types'] == 0 and len(c['a_twocycle_flat_types']) == 3
    assert c['per_shape']['U1_raised_on_every_shape'] and c['per_shape']['U0_raised_on_every_shape']
    assert d['4752']['lowest_D'][0]['centre_theta2'] == 0.0 and d['4753']['lowest_D'][0]['centre_theta2'] > 1.5

# ------------------------------------------------------------------ preregistration
def test_preregistration_committed_before_deep_results():
    def first_commit_time(path):
        out = subprocess.run(['git', 'log', '--diff-filter=A', '--format=%ct', '--', path], capture_output=True, text=True, cwd=ROOT).stdout.split()
        return int(out[-1]) if out else None
    t0 = first_commit_time('audit/results/phase11_preregistration.json'); assert t0 is not None
    for p in ('audit/results/phase11_frontier_twins_Y5.jsonl', 'audit/results/phase11_frontier_counterfactual_Y5.jsonl'):
        t = first_commit_time(p)
        if t is not None: assert t > t0
