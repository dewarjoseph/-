"""Phase XII regression, reproduction and adversarial tests.

Three kinds of test.
- Recomputations with the independent implementation (audit/phase12_independent.py, which imports no phase 5-11 code): its
  decoder, legal types, exact supertile bounds and small certificates agree with the certifying code.
- Artifact checks: every number of deliverables/PHASE12_REPORT.md is read back from audit/results and re-derived where possible
  (exact rationals re-compared, flags recomputed).
- Adversarial tests designed to make a claim fail: a certificate above the floor must fail and report its failing balls; a corrupted
  link must break the gauge identity; a non-dyadic shift must be refused; the falsified defect law must stay recorded as falsified.
A passing test shows consistency, not truth; the proofs are in the report.
Run: python -m pytest -q tests/test_phase12.py"""
import os, sys, json, math, subprocess, itertools
from fractions import Fraction
import numpy as np
import pytest
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__))); AUD = os.path.join(ROOT, 'audit'); RES = os.path.join(AUD, 'results')
sys.path.insert(0, AUD)
os.environ.setdefault('OMP_NUM_THREADS', '1')
import phase12_independent as I
def J(n): return json.load(open(os.path.join(RES, n)))
def JL(n): return [json.loads(l) for l in open(os.path.join(RES, n))]
ORBIT = {184323, 184338, 184342, 539311, 539291, 539288}

# ------------------------------------------------------------------ the independent implementation
def test_independent_decoder():
    import phase11_chair as C
    assert all(tuple(I.decoration(i)) == C.proper_decoration(i) for i in range(6561))
    for j in list(range(0, 6 ** 8, 4999)) + sorted(ORBIT):
        assert tuple(I.decoration('x%d' % j)) == C.extended_decoration(j)

def test_independent_links_match_phase11():
    import phase11_chair as C
    f, T = I.supertile(I.decoration('4753'), 2); G, T2 = C.supertile(C.rule('4753'), 2)
    assert np.array_equal(T, T2) and np.array_equal(I.FARR[f], G)
    a, b, k = C.Patch(G, T2).panels(); U = C.link_matrices(G, a, b, k)
    sig = [np.array([[0, 1], [1, 0]]), np.array([[0, -1j], [1j, 0]]), np.array([[1, 0], [0, -1]])]
    for (aa, bb, kk), u in zip(zip(a, b, k), U):                     # quaternion q_k = -i sigma_k
        q = I.Q8[I.LINK[f[aa], f[bb], kk]]
        assert np.allclose(u, q[0] * np.eye(2) + sum(q[1 + m] * (-1j) * sig[m] for m in range(3)))

@pytest.mark.parametrize('spec,n', [('4752', 72), ('4753', 90), ('x539288', 79)])
def test_independent_legal_types(spec, n):
    ty, n0 = I.legal_types(I.decoration(spec)); assert len(ty) == n

def test_independent_exact_Y3_matches():
    lam, q = I.Y('4753', 3); assert abs(float(q) - 9.955918832466624) < 1e-9 and q >= Fraction(lam) - Fraction(1, 10 ** 9)

def test_independent_small_certificate_and_adversarial(tmp_path, monkeypatch):
    monkeypatch.setattr(I, 'OUT', str(tmp_path / 'ind.jsonl'))
    ok = I.certify('4752', 6, 3, 1, '3833131/1048576', 'test_ok')
    assert ok['all_balls_certified'] and ok['distinct_balls'] == 325 and ok['Lambda_R_certified'] > 3.6555585
    bad = I.certify('4752', 6, 3, 1, '3.6556', 'test_above_floor')       # Lambda_6 = 3.65555995: must fail, with the balls named
    assert not bad['all_balls_certified'] and bad['balls_failing'] >= 1 and all(3.6555 < b['lambda_float'] < 3.6556 for b in bad['failing_balls_lowest'])

def test_independent_shift_must_be_exact():
    import scipy.sparse as sps
    H = sps.csr_matrix(np.diag([24.0, 24.0]) - np.array([[0, 1.0], [1.0, 0]]))
    with pytest.raises(AssertionError): I.higham(H, 0.1, 0.0)            # 24 - 0.1 is not exact in binary

def test_independent_R20_reproduction():
    rows = [r for r in JL('phase12_independent.jsonl') if r.get('tag') == 'independent_1387_R20']; assert rows
    r = rows[-1]; assert r['all_balls_certified'] and r['rejected_incomplete'] == 0 and r['distinct_balls'] == 24571
    assert r['centres'] == 2949120 and r['Lambda_R_certified'] > 9.11049 and 'phase12_independent' in r['implementation']

# ------------------------------------------------------------------ Part I: the radius-20 certificate and the frontier
def test_R20_certificate_record():
    r = [x for x in JL('phase11_cert.jsonl') if x.get('tag') == 'target_1387_R20'][-1]
    assert r['all_balls_certified'] and r['distinct_balls'] == 24571 and r['mu'] == '9553051/1048576'
    assert Fraction(math.floor(Fraction('9.1105') * 2 ** 20), 2 ** 20) == Fraction(9553051, 1048576)

def test_frontier_table():
    d = J('phase12_frontier.json'); st = {r['rule']: r['status'] for r in d['rows']}
    assert st['1387'] == 'leader' and {st[x] for x in ('539311', '1389', '539291')} == {'contender'}
    assert {st[x] for x in ('1391', '539288', 'FR30 (1386)')} == {'proven_inferior'}
    L = Fraction(d['L_leader'])
    for r in d['rows']:
        if r['status'] == 'proven_inferior': assert Fraction(r['U_exact']) < L
        if r['status'] == 'contender': assert Fraction(r['U_exact']) >= L

# ------------------------------------------------------------------ Part II: the Orbit Lemma
def test_orbit_lemma_records():
    d = J('phase12_orbit.json')['lemma']
    assert d['a_pose_identity'] and d['a_rhoQ_preserves_cubes'] and d['b_link_identity_max_error'] < 1e-14 and d['b_exact_identity_holds']
    assert d['c_representatives_checked'] == 280332 and d['c_level1_spectrum_constant_on_right_orbits_max_dev'] < 1e-12
    assert d['d_level2_pairwise_disjoint'] and d['e_separated'] and d['e_539288_is_1387_times_Q'] == [[0, 2, 1]]

def test_orbit_lemma_stabiliser_clause():
    """1386 is fixed by (x y); 1386.(x y) = 539315 (FR30's mirror); the lemma's clause (d) gives equal floors; checked live at T_3"""
    import phase12_orbit as O
    d = np.array([O.PIDX[p] for p in I.decoration('1386')]); q = I.PERM3.index((1, 0, 2))
    assert int(O.conj_index(d[None], q)[0]) == int(O.index(d)) and int(O.rep(O.right(d, q)[None])[0]) == 539315
    a, _ = I.Y('1386', 3); b, _ = I.Y('x539315', 3); assert abs(a - b) < 1e-10
    law = J('phase12_orbit.json')['defect_law']; assert law['H0_pass'] and law['pairs_by_delta']['0'] == 912

def test_orbit_level1_equal_level2_split_live():
    import phase12_orbit as O
    d0 = np.array([O.PIDX[p] for p in I.decoration('4753')]); v1, v2 = [], []
    for q in range(6):
        dq = [I.PERM3[x] for x in O.right(d0, q)]
        for L, acc in ((1, v1), (2, v2)):
            f, T = I.supertile(dq, L); acc.append(np.linalg.eigvalsh(I.operator(f, T).toarray())[:4])
    assert max(np.abs(v - v1[0]).max() for v in v1) < 1e-12 and len({round(v[0], 6) for v in v2}) == 6

def test_defect_law_falsified_as_recorded():
    pre = J('phase12_preregistration_delta.json'); law = J('phase12_orbit.json')['defect_law']
    assert '0.3' in pre['hypotheses']['H1_rank_law'] and law['H1_spearman_delta_vs_abs_dY3'] < 0.3 and not law['H1_pass'] and not law['H2_pass']
    def first_commit(path):
        out = subprocess.run(['git', 'log', '--diff-filter=A', '--format=%ct', '--', path], capture_output=True, text=True, cwd=ROOT).stdout.split()
        return int(out[-1]) if out else None
    t0 = first_commit('audit/results/phase12_preregistration_delta.json'); t1 = first_commit('audit/results/phase12_orbit.json')
    assert t0 is not None and (t1 is None or t1 >= t0)

def test_adversarial_corrupted_link_breaks_gauge_identity():
    """flip the sign of one entry of the link table: the exact integer identity x u xbar = |x|^2 u' must then fail"""
    x = (0, -1, 0, 1); Qf = I.fidx(I.pmat((2, 1, 0))); xb = (x[0], -x[1], -x[2], -x[3])
    u = I.Q8[I.LINK[3, 17, 1]]; up = I.Q8[I.LINK[I.FMUL[3, Qf], I.FMUL[17, Qf], 1]]
    assert I.qmul(I.qmul(x, u), xb) == tuple(2 * c for c in up)
    bad = tuple(-c for c in up); assert I.qmul(I.qmul(x, u), xb) != tuple(2 * c for c in bad)

def test_funnel_clustering_record():
    f = J('phase12_orbit.json')['funnel']
    assert f['representatives'] == 280332 and 0.5 < f['Y3_variance_explained_by_right_orbits'] < 0.7
    assert f['Y3_variance_explained_random_partition_same_sizes'] < 0.2 and f['X4_survivors'] == 38

# ------------------------------------------------------------------ Part III and VI
def test_plaquette_counts_almost_injective_on_census():
    import collections
    cen = J('phase10_census.json')['classes']; g = collections.Counter((r['plaq_L3']['+1'], r['plaq_L3']['-1'], r['plaq_L3']['i'] + r['plaq_L3']['j'] + r['plaq_L3']['k']) for r in cen)
    assert len(g) == 1096 and len(cen) == 1098

def test_transport_bound_records_and_live():
    d = J('phase12_transport.json')
    for k in ('4753', '1389', '1391', 'x539311', 'x539288'): assert abs(d[k]['bound'] - 1.6992660162749642) < 1e-12
    assert abs(d['4752']['bound'] - 1.5687416572832378) < 1e-12
    import phase12_transport as Tr
    r = Tr.bound('4752'); assert abs(r['bound'] - d['4752']['bound']) < 1e-12 and r['W'] == 4

def test_transport_theorem_on_random_graphs():
    """Theorem 6.1 on random multigraphs with Q8 links: lambda_min(H) >= inf_v alpha(v)/W for the family of all 2-cycles"""
    rng = np.random.default_rng(3)
    for _ in range(30):
        n = 6; edges = [(int(a), int(b)) for a, b in rng.integers(0, n, (14, 2)) if a != b]
        U = [I.Q8[int(rng.integers(0, 8))] for _ in edges]
        H = np.zeros((4 * n, 4 * n)); deg = np.zeros(n)
        for (a, b), q in zip(edges, U):
            L = I.Lmat(q); H[4 * a:4 * a + 4, 4 * b:4 * b + 4] -= L; H[4 * b:4 * b + 4, 4 * a:4 * a + 4] -= L.T; deg[a] += 1; deg[b] += 1
        H += np.diag(np.repeat(deg, 4)); lam = np.linalg.eigvalsh(H)[0]
        cyc = []
        for i, j in itertools.combinations(range(len(edges)), 2):
            (a, b), (c, d) = edges[i], edges[j]
            if {a, b} != {c, d}: continue
            u2 = U[j] if (c, d) == (a, b) else (U[j][0], -U[j][1], -U[j][2], -U[j][3])
            W = I.qmul(U[i], (u2[0], -u2[1], -u2[2], -u2[3]))
            th = 0.0 if W == (1, 0, 0, 0) else math.pi if W == (-1, 0, 0, 0) else math.pi / 2
            cyc.append(((a, b), (i, j), 2 * (1 - math.cos(th / 2))))
        if not cyc: continue
        load = np.zeros(len(edges)); alpha = np.zeros(n)
        for (a, b), (i, j), l in cyc: load[i] += 1; load[j] += 1; alpha[a] += l; alpha[b] += l
        assert lam >= alpha.min() / load.max() - 1e-9

# ------------------------------------------------------------------ Part IX
def test_formal_checks():
    d = J('phase12_formal.json'); assert all(d['ims_edge_identity'].values()) and d['orbit_child_rule']['holds'] and d['shadow_formula']['holds']
    assert d['orbit_link_exact']['holds'] and 'not available' in d['lean']
    import phase12_formal as Fm
    assert Fm.orbit_child_rule()['violations'] == 0 and Fm.shadow_formula()['violations'] == 0

# ------------------------------------------------------------------ Part VII: the cube family
def test_cube_orbit_lemma_transfers():
    s = J('phase12_cube.json')['orbit']['spreads']
    assert s['pi/2:det+1:L1_spread'] < 1e-12 and s['pi/2:det-1:L1_spread'] < 1e-12            # all 48 Q at theta = pi/2
    assert s['pi/5:det+1:L1_spread'] < 1e-12 and s['pi/5:det-1:L1_spread'] < 1e-12            # within each parity
    rows = J('phase12_cube.json')['orbit']['rows']
    p, m = [r['pi/5:L1']['spinor'] for r in rows if r['det'] == 1], [r['pi/5:L1']['spinor'] for r in rows if r['det'] == -1]
    assert abs(p[0] - m[0]) > 1e-3                                                              # improper Q: theta -> -theta
    assert s['pi/2:det+1:L2_spread'] > 0.1                                                      # broken from level 2 on

def test_cube_flat_rule():
    lv = J('phase12_cube.json')['flat_identity_rule']['levels']
    for L, r in lv.items():
        assert abs(r['spinor'] - 6 * (1 - math.cos(math.pi / (2 ** int(L) + 1)))) < 1e-9 and abs(r['spinor'] - r['adjoint']) < 1e-9

def test_cube_representation_order_flips():
    r0 = J('phase12_cube.json')['orbit']['rows'][0]
    assert r0['pi/2:L3']['adjoint'] < r0['pi/2:L3']['spinor'] and r0['pi/5:L3']['adjoint'] > r0['pi/5:L3']['spinor']
    assert abs(r0['pi/2:L3']['adjoint'] - min(r0['pi/2:L3']['chi%d' % k] for k in (1, 2, 3))) < 1e-9

# ------------------------------------------------------------------ Part VIII: the preregistered prediction
def test_prediction_preregistered_before_targets():
    def first_commit(path):
        out = subprocess.run(['git', 'log', '--diff-filter=A', '--format=%ct', '--', path], capture_output=True, text=True, cwd=ROOT).stdout.split()
        return int(out[-1]) if out else None
    t0 = first_commit('audit/results/phase12_preregistration.json'); t1 = first_commit('audit/results/phase12_y5_census.jsonl')
    assert t0 is not None and (t1 is None or t1 > t0)
    pre = J('phase12_preregistration.json'); assert len(pre['split']['train']) == len(pre['split']['test']) == 549
    assert not set(pre['split']['train']) & set(pre['split']['test'])

def test_prediction_results():
    d = J('phase12_predict.json'); assert d['n_test'] == 549 and d['phase10_Y5_max_deviation'] < 1e-6
    for fam, r in d['families'].items(): assert -1 <= r['spearman_test'] <= 1 and 0 <= r['interval_90_coverage_test'] <= 1

# ------------------------------------------------------------------ Part V: the intervention
def test_intervention_both_signs():
    rows = JL('phase12_intervention.jsonl'); base = {(r['base'], r['R']): r for r in rows if r['change'] and r['change']['slot'] is None}
    deltas = [r['Lambda_float'] - base[(r['base'], r['R'])]['Lambda_float'] for r in rows if (r['base'], r['R']) in base and r['change'] and r['change']['slot'] is not None]
    assert any(x > 0 for x in deltas) and any(x < 0 for x in deltas)                            # no universal monotonicity

# ------------------------------------------------------------------ ledger
def test_phase12_ledger_links():
    d = J('phase12_ledger.json'); names = {n for n in globals() if n.startswith('test_')}
    assert len(d['claims']) >= 20 and len(d['corrections']) == 5
    p11 = open(os.path.join(ROOT, 'tests', 'test_phase11.py')).read()
    for c in d['claims']:
        for t in c['test'].split(', '):
            if t == '-': continue
            if t.startswith('phase11:'): assert f'def {t[8:]}(' in p11, t
            else: assert t in names, t

def test_stored_certificate_shifts_exact():
    """phase11_chair.banded_cert's assertion (d - mu) + mu == d does not prove the shift exact (24 - 0.1 passes it); every stored
    certificate is nevertheless exact because its mu is dyadic with a small numerator: 24 - mu is then representable"""
    for name in ('phase11_cert.jsonl', 'phase12_independent.jsonl'):
        for r in JL(name):
            if not r.get('mu'): continue
            mu = Fraction(r['mu']); assert mu.denominator & (mu.denominator - 1) == 0 and mu.denominator <= 2 ** 30
            assert Fraction(24.0 - float(mu)) == 24 - mu

def test_closure_explains_every_tie():
    c = J('phase12_orbit.json')['closure']
    assert c['pairs'] == 1401660 and c['ties'] >= 912 and c['ties_unexplained'] == 0 and c['explained_but_not_tied'] == 0
