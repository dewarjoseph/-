"""Phase VII checks (deliverables/PHASE7_REPORT.md).  Fast tests recompute small statements from scratch; the remaining tests
check the stored results of the long runs (audit/results/phase7_*.json) for internal consistency.
Run: python -m pytest -q tests/test_phase7.py"""
import os, sys, json, math, itertools
from fractions import Fraction
import numpy as np
import pytest
HERE = os.path.dirname(os.path.abspath(__file__)); AUD = os.path.join(HERE, '..', 'audit'); sys.path.insert(0, AUD)
RES = os.path.join(AUD, 'results')
def load(name): return json.load(open(os.path.join(RES, name)))


# ------------------------------------------------------------------ II.1 forced curvature
def test_two_cycle_formula_matches_explicit_products():
    """Lemma F'.1 with det factors: W = 1 iff det M_a det M_b (M_a^T e_m . M_b^T e_m) = 1, against explicit Q8 products,
    for all 6561 proper choices and 30000 random O(3)-compatible choices."""
    import phase7_adversarial as A
    proper = np.array([p for p in itertools.product(range(6), repeat=8) if all(A.DET[t, p[t]] == 1 for t in range(8))], np.int8)
    assert len(proper) == 6561
    P = np.concatenate([proper, np.random.default_rng(7).integers(0, 6, (30000, 8)).astype(np.int8)])
    tw = A.analyse(P)[5]
    FRA = np.array([[A.FR[t][p] for p in range(6)] for t in range(8)])               # (8, 6, 3, 3)
    for i, ((a, b), k, l) in enumerate(A.TWO):
        m = 3 - k - l; ua = FRA[a, P[:, a], m]; ub = FRA[b, P[:, b], m]                # rows m = M^T e_m
        pred = A.DET[a, P[:, a]] * A.DET[b, P[:, b]] * (ua * ub).sum(1) == 1
        assert np.array_equal(pred, tw[:, i] == 0)


def test_counting_lemma_and_sharpness():
    """>= 12 of 21 two-cycles non-trivial for every compatible frame (Python mirror of certificates/Phase7Counting.lean),
    attained; the Phase VI list of 9 is forced exactly for proper frames."""
    import phase7_adversarial as A
    assert len(A.TWO) == 21 and {p for p, k, l in A.TWO} == {(0, t) for t in range(1, 8)}
    P = np.array(list(itertools.product(range(6), repeat=8)), np.int8)[::37]          # 45 396 choices, both parities
    ntw = A.analyse(P)[3]; assert ntw.min() >= 12
    adv = load('phase7_adversarial.json')
    assert adv['all']['count'] == 6 ** 8 and adv['all']['min_nontrivial_two_cycle_configs'] == 12 and adv['all']['pure_gauge'] == 0
    assert adv['proper']['all_forced_nontrivial'] and not adv['improper']['all_forced_nontrivial']
    ex = adv['improper_forced_failure_example']; assert -1 in ex['det'] and ex['nontrivial_two_cycle_configs'] >= 12


def test_lean_counting_certificate_is_complete():
    src = open(os.path.join(HERE, '..', 'certificates', 'Phase7Counting.lean'), encoding='utf-8').read()
    for name in ('octant_bound', 'total_bound', 'bound_attained', 'forced_proper', 'forced_fails_improper'): assert f'theorem {name}' in src
    assert 'sorry' not in src and 'native_decide' not in src


# ------------------------------------------------------------------ II.2 uniform floor
def test_uniform_floor_certificates():
    adv = load('phase7_adversarial.json')
    assert adv['certificate_proper']['failures'] == 0 and adv['certificate_proper']['c'] == '167/100'
    for tag in ('proper_sharper', 'improper'):
        c = adv[f'certificate_{tag}']; assert c['failures'] == 0 and c['c'] == '41789/25000' and c['rejects_min_plus_1e-5']
    assert adv['certificate_improper']['gauge_classes'] > 1_600_000
    z = adv['zero_mode']; assert z['free_trivial_kernel_dim'] == 2 and z['pinned_trivial_lambda_min'] > 1


# ------------------------------------------------------------------ I.4 localization (IMS)
def c_closed(eta): return (math.pi * (1 - eta / 2) * math.sin(math.pi * eta) + 1 - math.cos(math.pi * eta)) / (math.pi ** 2 * eta)

@pytest.mark.parametrize('h,rho', [(1.8, 4.2), (2.1, 6.2), (2.0, 10.0), (3.5, 5.0)])
def test_ims_overlap_closed_form(h, rho):
    """int phi(z) phi(z+h) dz / ||phi||^2 for the Dirichlet ball ground state, by the 3D radial convolution formula."""
    from scipy.integrate import quad
    F = lambda r: math.sin(math.pi * r / rho) if 0 <= r <= rho else 0.0
    inner = lambda r: quad(F, abs(h - r), min(h + r, rho))[0]
    C = 2 * math.pi / h * quad(lambda r: F(r) * inner(r), 0, rho, limit=200)[0]
    assert abs(C / (2 * math.pi * rho) - c_closed(h / rho)) < 1e-8


def test_ims_amplification_interval():
    import phase7_ims as I
    rho = Fraction(1089, 175); amp = I.amp_table([196 * 4, 196 * 3, 900], rho)
    for d2, (v, e) in amp.items():
        assert abs(v - 1 / c_closed(math.sqrt(d2) / 14 / float(rho))) < 1e-12 and 0 < e < 1e-12 and v > 1


def test_blocked_cholesky():
    import phase7_ims as I
    rng = np.random.default_rng(0); B = rng.standard_normal((300, 300)); A = B @ B.T + 50 * np.eye(300)
    X = np.tril(A.copy()); assert I.cholesky_lower(X, nb=32); assert np.abs(np.tril(X) - np.linalg.cholesky(A)).max() < 1e-10
    lam = np.linalg.eigvalsh(A)[0]; assert not I.cholesky_lower(np.tril(A - (lam + 1e-6) * np.eye(300)), nb=32)


def test_ims_results():
    d = load('phase7_ims.json'); Rs = sorted(int(r) for r in d if r.isdigit()); assert Rs[:2] == [6, 8]
    L = [Fraction(d[str(R)]['L_R_certified']) for R in Rs]
    assert all(x < y for x, y in zip(L, L[1:])) and L[1] > Fraction(656, 100)            # the local bounds climb
    for R in Rs:
        r = d[str(R)]; assert Fraction(r['L_R_certified']) < Fraction(r['mu']) and r['max_delta'] < 1e-6
        if 'plain' in r: assert Fraction(r['L_R_certified']) < Fraction(r['plain']['certified_min'])
    assert d['6']['plain']['exact_bareiss_minimiser']['H_minus_mu_posdef'] and d['6']['plain']['exact_bareiss_minimiser']['H_minus_lambda_plus_1e-6_not_posdef']
    assert Fraction(d['constants']['S_1']) == Fraction(4734, 49) and d['constants']['r_c_squared'] == '619/196'
    assert max(L) < Fraction(87649120247, 10 ** 10)                                     # below the certified upper bound (V-E)


# ------------------------------------------------------------------ I.2 / I.3 block bounds and approximants
def test_block_bounds_and_types():
    d = load('phase7_local.json'); t = d['types']
    assert t['sizes'] == {'1': 72, '2': 165, '3': 445, '4': 762} and all(t[f'census_L6_R{R}']['equal'] for R in (1, 2, 3, 4))
    assert all(x['max_dev'] == 0.0 for x in d['identity'])
    L = {R: Fraction(d['bounds'][str(R)]['L_R_certified']) for R in (2, 3, 4)}
    assert L[2] >= Fraction(72147403, 18000000) and L[3] > L[2] > L[4]                    # the block method is not monotone
    ap = d['approximants']; assert all(ap[str(k)]['1']['illegal'] > 0 for k in (1, 2, 3, 4))  # no V-A approximant is in T_1


def test_periodic_search_controls_and_small_periods():
    import phase7_periodic_search as S
    V1 = S.legal_V1(); s1, types1 = S.p1_on_torus()
    assert sum(1 for k in types1 if k not in V1) == 7                                    # = phase7_local's P_1 count
    assert S.Search(S.Torus(1, (1, 2, 4)), None).run().solutions                          # crystal without legality
    for phi in ((1, 2, 4), (1, 4, 2)):
        s = S.Search(S.Torus(1, phi), V1).run(); assert not s.solutions and s.nodes < s.limit         # no 1-legal crystal
    d = load('phase7_periodic_search.json')
    assert d['controls']['P1_found_with_P1_types'] and d['controls']['crystal_found_without_legality']
    assert all(r['solutions_found'] == 0 for r in d['search'])


def test_recognizability():
    d = load('phase7_recognizability.json'); assert d['1']['ambiguous_types'] == 0 and d['2']['ambiguous_types'] == 0


# ------------------------------------------------------------------ II.3 Abelian vs non-Abelian, same normalisation
def test_abelian_check():
    d = load('phase7_abelian_check.json'); z = d['reflection_only_Z2']
    assert abs(Fraction(z['4']['rayleigh_upper_exact']) - Fraction(1075868655136284, 281475010395005)) < Fraction(1, 10 ** 9)
    assert z['4']['abelian'] and not d['fr30']['4']['abelian'] and Fraction(z['5']['rayleigh_upper_exact']) < Fraction(z['4']['rayleigh_upper_exact'])
    ims = load('phase7_ims.json'); assert max(Fraction(ims[r]['L_R_certified']) for r in ims if r.isdigit()) > Fraction(z['5']['rayleigh_upper_exact'])
    assert Fraction(d['trivial']['5']['rayleigh_upper_exact']) < Fraction(1, 7)
