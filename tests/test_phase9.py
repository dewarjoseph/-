"""Phase IX tests (deliverables/PHASE9_REPORT.md).  Fast tests recompute the exact statements about the rule pair 937/938 from
the independent construction in audit/phase9_pair.py; JSON tests check stored outputs of the longer runs for consistency.
Run: python -m pytest -q tests/test_phase9.py"""
import os, sys, json, math, types
from fractions import Fraction
import numpy as np
import pytest
HERE = os.path.dirname(os.path.abspath(__file__)); AUD = os.path.join(HERE, '..', 'audit'); sys.path.insert(0, AUD)
sys.modules.setdefault('resource', types.SimpleNamespace(getrusage=lambda *a: types.SimpleNamespace(ru_maxrss=0), RUSAGE_SELF=0))
RES = os.path.join(AUD, 'results')
def load(n): return json.load(open(os.path.join(RES, n)))
import phase9_pair as P9


@pytest.fixture(scope='module')
def pair3():
    A = P9.build([P9.decoration(937)] * 3); B = P9.build([P9.decoration(938)] * 3, ref=A['grid']); return A, B


def test_decoration_map_and_orbits_match_census():
    import phase5b_sweep as sw
    for i in (0, 1, 937, 938, 4752, 6560): assert P9.decoration(i) == sw.decoration(i)
    orb = lambda i: sorted({P9.index_of(P9.conj_dec(P9.decoration(i), Q)) for Q in P9.PERMS})
    assert orb(937) == [937, 1190, 3943, 4142, 4502, 4951] and orb(938) == [938, 1189, 3944, 4141, 4501, 4952]
    d7, d8 = P9.decoration(937), P9.decoration(938)
    assert [k for k in d7 if d7[k] != d8[k]] == ['0']                            # they differ in the centre child only


def test_independent_operator_reproduces_census(pair3):
    import phase5b_sweep as sw
    rec = {r['index']: r for r in load('phase5b_sweep.json')['records'] if r['index'] in (937, 938, sw.FR30_INDEX)}
    A, B = pair3
    assert abs(np.linalg.eigvalsh(A['H'].toarray())[0] - rec[937]['L3']['lambda'][0]) < 1e-9
    assert abs(np.linalg.eigvalsh(B['H'].toarray())[0] - rec[938]['L3']['lambda'][0]) < 1e-9
    F = P9.build([P9.decoration(sw.FR30_INDEX)] * 3)
    assert abs(np.linalg.eigvalsh(F['H'].toarray())[0] - 9.378470210300526) < 1e-9


def test_same_geometry_same_counts_different_fields(pair3):
    A, B = pair3
    assert all(np.array_equal(A[k], B[k]) for k in ('a', 'b', 'ax', 'T'))       # same chairs, same panels
    _, ca = P9.plaquettes(A); _, cb = P9.plaquettes(B); _, ta = P9.two_cycles(A); _, tb = P9.two_cycles(B)
    assert P9.class_counts(ca) == P9.class_counts(cb) and P9.class_counts(ta) == P9.class_counts(tb)
    assert (ca != cb).sum() == 2058 and (ta != tb).sum() == 1464                   # equal counts, different arrangements
    assert (P9.trace_of(ca) != P9.trace_of(cb)).sum() == 1116 and (P9.trace_of(ta) != P9.trace_of(tb)).sum() == 756   # SU(2)-invariant part


def test_certified_level3_separation(pair3):
    A, B = pair3
    q938 = P9.rayleigh_upper(B['H'])                                              # exact: lambda_min(938) <= q938
    lo937 = P9.certified_lower(A['H'], Fraction(8903484, 2 ** 20))                # rigorous: lambda_min(937) >= lo937
    assert lo937 is not None and lo937 - float(q938) > 0.2775


def test_first_differing_moment_is_four(pair3):
    A, B = pair3
    ta, _ = P9.int_moments(A['H'], 5); tb, _ = P9.int_moments(B['H'], 5)
    assert ta[:3] == tb[:3] and ta[3] - tb[3] == 2976 and ta[4] - tb[4] == -438840
    wa, wb = P9.walk4(A), P9.walk4(B)
    assert wa['P1'] == wb['P1'] and wa['P2'] - wb['P2'] == -1536 and wa['P4'] - wb['P4'] == 6048 and wa['total'] == ta[3]


def test_stored_pair_results():
    p = load('phase9_pair.json')
    for L in ('3', '4', '5'):
        r = p['levels'][L]; assert r['class_counts']['937'] == r['class_counts']['938'] and r['Y']['937'] - r['Y']['938'] > 0.24
    assert not p['same_orbit']


def test_ladder_reproduces_phase8_and_decides_preregistered_test():
    """the independent ladder reproduces FR30's 72 legal 1-star types and Phase VIII's U_1; the stored m <= 1 ladder gives the
    pre-registered verdict 'null supported' for 937/938"""
    import phase5b_sweep as sw
    dec = P9.decoration(sw.FR30_INDEX); S = P9.build([dec] * 5); types_ = P9.one_star_types(S); assert len(types_) == 72
    u1 = min(P9.lam_min(P9.patch_H(*P9.inflate(S['G'][m], S['T'][m], dec))) for m in types_.values())
    assert abs(u1 - load('phase8_patch_bounds.json')['U']['1']['min']) < 1e-9
    lad = load('phase9_ladder_m01.json'); pre = load('phase9_preregistration.json'); pair = load('phase9_pair.json')
    d1 = lad['diff_938_minus_937']['1']; ds = pair['levels']['5']['Y']['938'] - pair['levels']['5']['Y']['937']
    assert 'Delta_1' in pre['decision_rule']['null_supported_hierarchy_falsified'] and d1 * ds > 0 and abs(d1 - ds) <= 0.10


def test_finest_substitution_step_carries_the_difference():
    st = load('phase9_steps.json')
    for L, r in st['levels'].items():
        L = int(L); me = r['main_effect_of_step']; diff = r['Y938'] - r['Y937']
        assert abs(me[str(L)]) > 0.9 * abs(diff) and all(abs(me[str(j)]) < 0.015 for j in range(1, L))


def test_level4_certificate_and_census_structure():
    c = load('phase9_cert4.json'); assert c['certified_separation'] > 0.25 and c['937']['lower'] > c['938']['upper']
    s = load('phase9_state.json'); res = s['results']
    assert s['orbits'] == 1125 and s['gauge_classes'] == 1098 and s['isospectral_but_not_gauge_equivalent'] == 0
    assert res['counts']['collisions_with_different_Y3'] == 1 and all(r['collisions_with_different_Y3'] == 0 for k, r in res.items() if k != 'counts')
    assert all(r[f'{t}_{m}_fr30_pred'] < r[f'{t}_fr30_true'] for r in res.values() for t in ('Y3', 'Y4') for m in ('ols', 'knn'))   # FR30 underpredicted
    cc = load('phase9_count_closure.json'); assert cc['L3_vectors_with_several_L4_vectors'] == 0 and cc['L3_count_vectors_with_different_Y3'] == 1


def test_full_ladder_matches_phase8_and_stays_local():
    lad = load('phase9_ladder.json'); pb = load('phase8_patch_bounds.json'); pair = load('phase9_pair.json')
    u = lad['rules']['FR30']['U_m']
    for m in (1, 2, 3): assert abs(u[m] - pb['U'][str(m)]['min']) < 1e-6        # independent code = Phase VIII chain
    ds = pair['levels']['5']['Y']['938'] - pair['levels']['5']['Y']['937']
    assert all(v < 0 and abs(v - ds) < 0.07 for v in lad['diff_938_minus_937'].values())   # 74-94 % of the gap at every rung
