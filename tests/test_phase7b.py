"""Phase VII-B targeted tests (deliverables/PHASE7_REPORT.md, ledger audit/results/phase7b_ledger.json).

Logical independence (see the report, section 2): the fast tests below recompute from definitions using
phase7_adversarial (own Q8 table, own level-1 geometry), independent_clifford_q8_audit (separate tile generator and matrix
links) and phase7_local; they share the FR30 decoration and the pose convention (the definitions).  JSON tests check the
stored outputs of the long runs for internal consistency; they are not independent proofs.
Run: python -m pytest -q tests/test_phase7b.py"""
import os, sys, json, math, itertools
from fractions import Fraction
import numpy as np
import pytest
HERE = os.path.dirname(os.path.abspath(__file__)); AUD = os.path.join(HERE, '..', 'audit'); sys.path.insert(0, AUD)
RES = os.path.join(AUD, 'results')
def load(name): return json.load(open(os.path.join(RES, name)))
SIG = [np.array([[0, 1], [1, 0]], complex), np.array([[0, -1j], [1j, 0]], complex), np.array([[1, 0], [0, -1]], complex)]


# ------------------------------------------------------------------ Q8 multiplication and orientation conventions
def test_q8_table_conventions():
    import phase7_adversarial as A
    q = [A.MAT[2], A.MAT[4], A.MAT[6]]
    for k in range(3): assert np.allclose(q[k], -1j * SIG[k]) and np.allclose(q[k] @ q[k], -np.eye(2))
    assert np.allclose(q[0] @ q[1], q[2]) and np.allclose(q[1] @ q[2], q[0]) and np.allclose(q[2] @ q[0], q[1])
    for a in range(8):
        for b in range(8): assert np.allclose(A.MAT[a] @ A.MAT[b], A.MAT[A.MUL[a, b]])
        assert np.allclose(A.MAT[A.INVQ[a]], np.linalg.inv(A.MAT[a]))


def test_link_identity_exhaustive_over_signed_frames():
    """Pauli-identity links (phase7_adversarial.link_q) == matrix links (independent_clifford_q8_audit) for all 48 x 48 x 3;
    reverse crossing gives the inverse."""
    import phase7_adversarial as A
    from independent_clifford_q8_audit import clifford_link
    S = [np.diag(s) @ np.eye(3, dtype=int)[list(p)] for p in itertools.permutations(range(3)) for s in itertools.product((1, -1), repeat=3)]
    for Ma in S:
        for Mb in S:
            for k in range(3):
                n = np.zeros(3, int); n[k] = 1; C = clifford_link(Ma, Mb, n)
                assert np.allclose(C, A.MAT[A.link_q(Ma, Mb, k)]) and np.allclose(clifford_link(Mb, Ma, n), np.linalg.inv(C))
                assert np.allclose(clifford_link(Ma, Mb, -n), C)


# ------------------------------------------------------------------ gauge invariance
def test_gauge_invariance_of_spectrum_and_flux():
    from independent_clifford_q8_audit import FR30, tiles_at_level, panel_edges
    from phase5a_controls import clifford_links, build_H
    tl = tiles_at_level(FR30, 2); _, ed = panel_edges(tl); links = clifford_links(tl, ed); n = len(tl)
    H = build_H(n, ed, links, np.full(n, 24.0)).toarray(); rng = np.random.default_rng(3)
    g = []
    for _ in range(n):
        v = rng.standard_normal(4); v /= np.linalg.norm(v); g.append(v[0] * np.eye(2) + 1j * (v[1] * SIG[0] + v[2] * SIG[1] + v[3] * SIG[2]))
    Gm = np.zeros((2 * n, 2 * n), complex)
    for a in range(n): Gm[2*a:2*a+2, 2*a:2*a+2] = g[a]
    H2 = Gm @ H @ Gm.conj().T
    assert np.allclose(np.linalg.eigvalsh(H), np.linalg.eigvalsh(H2), atol=1e-10)
    # transformed links are g_a U g_b^-1 and the operator built from them equals H2
    links2 = [g[e[0]] @ L @ g[e[1]].conj().T for e, L in zip(ed, links)]
    assert np.allclose(build_H(n, ed, links2, np.full(n, 24.0)).toarray(), H2, atol=1e-12)


# ------------------------------------------------------------------ proper / improper edge cases and gauge classes
def test_constant_pi_fields_are_the_reflection_only_connection():
    import phase7_adversarial as A
    P = np.array([[p] * 8 for p in range(6)], np.int8); L = A.analyse(P)[0]
    assert all(np.array_equal(L[0], L[i]) for i in range(6))                          # identical links for all six
    assert set(np.unique(L).tolist()) <= {0, 1}                                         # +-1 only: Abelian Z2
    assert all(A.DET[t, 0] == int(np.prod(A.SIGMAS[t])) for t in range(8))            # improper wherever s has one minus sign
    assert (A.analyse(P)[3] >= 12).all()                                               # yet >= 12 non-trivial two-cycles


def test_gauge_class_counts():
    d = load('phase7b_consistency.json')
    assert d['assignments_all'] == 6 ** 8 and d['assignments_proper'] == 3 ** 8 and d['keys_proper'] == 6561 and d['keys_improper'] == 1672288
    assert d['keys_overlap_proper_improper'] == 0 and d['check_sum'] and d['swap_pairs_differ_by_minus_one_only']
    assert d['improper_class_sizes'] == {'1': 1671525, '2': 762, '6': 1}
    adv = load('phase7_adversarial.json'); assert adv['certificate_improper']['gauge_classes'] == d['keys_improper']


# ------------------------------------------------------------------ Python <-> Lean correspondence
def lean_defs():
    perms = [[0, 1, 2], [0, 2, 1], [1, 0, 2], [1, 2, 0], [2, 0, 1], [2, 1, 0]]
    sgn = lambda p: 1 if p in ([0, 1, 2], [1, 2, 0], [2, 0, 1]) else -1
    inv = lambda p, m: p.index(m)
    detV = lambda s, pv: s[0] * s[1] * s[2] * sgn(pv)
    trivial = lambda pc, pv, s, m: inv(pc, m) == inv(pv, m) and sgn(pc) * detV(s, pv) * s[m] == 1
    return perms, sgn, trivial

def test_lean_predicate_matches_explicit_holonomy():
    """certificates/Phase7Counting.lean's `trivial` (transcribed) == explicit Q8 two-cycle products in the actual level-1
    geometry, for every centre/octant permutation pair and every one of the 21 two-cycles.  Lean's list p = [pi 0, pi 1, pi 2]
    corresponds to the frame D_s P with P[i, p^-1(i)] = 1 (the theorems quantify over all permutations, so the relabelling
    p <-> p^-1, which preserves the sign, does not change them)."""
    import phase7_adversarial as A
    perms, sgn, trivial = lean_defs()
    pidx = {tuple(p): i for i, p in enumerate(A.PERMS)}
    for pc in perms:
        for pv in perms:
            pcinv = [pc.index(i) for i in range(3)]; pvinv = [pv.index(i) for i in range(3)]
            row = np.full(8, pidx[tuple(pvinv)], np.int8); row[0] = pidx[tuple(pcinv)]
            tw = A.analyse(row[None])[5][0]
            for i, ((a, b), k, l) in enumerate(A.TWO):
                m = 3 - k - l; s = list(A.SIGMAS[b])
                assert trivial(pc, pv, s, m) == (tw[i] == 0)
    src = open(os.path.join(HERE, '..', 'certificates', 'Phase7Counting.lean'), encoding='utf-8').read()
    assert '[[1,1,1], [1,1,-1], [1,-1,1], [1,-1,-1], [-1,1,1], [-1,1,-1], [-1,-1,1]]' in src
    assert sorted(tuple(s) for s in A.SIGMAS[1:]) == sorted([(1, 1, 1), (1, 1, -1), (1, -1, 1), (1, -1, -1), (-1, 1, 1), (-1, 1, -1), (-1, -1, 1)])


# ------------------------------------------------------------------ legal stars: completeness, closure, local rules
def test_local_rules_checks():
    d = load('phase7b_local_rules.json')
    assert d['V1'] == 72 and d['primitivity_power'] == 2 and d['R0']['max_roles_per_type'] == 1 and d['R0']['V1_subset_PhiV1']
    assert d['S']['distance1_siblings_inside_every_1star'] and d['A']['ok']
    assert d['B'].get('illegal_parent_stars', 0) == 0 and d['B']['parent_1stars_subset_V1'] and d['B']['configurations'] > 0
    assert d['child_distance_matrix'][2][7] == 2                                       # not every sibling is in a 1-star


def test_census_reconstruction():
    d = load('phase7b_census.json')
    assert [d['types'][str(R)] for R in (1, 2, 3, 4)] == [72, 165, 445, 762]
    assert all(d['equal_to_phase7_local'][str(R)] for R in (1, 2, 3, 4))


# ------------------------------------------------------------------ inequality directions
def test_compression_monotonicity():
    """Y_L >= Y_{L+1}: T_L is a principal block (compression) of T_{L+1} via its centre-child copy."""
    for name in ('trivial', 'reflection_only_Z2', 'fr30'):
        ys = [load('phase7_abelian_check.json')[name][str(L)]['lambda_min_float'] for L in (2, 3, 4, 5)]
        assert all(a >= b for a, b in zip(ys, ys[1:]))


def test_ims_directions_and_rates():
    d = load('phase7_ims.json'); c = load('phase7b_ims_check.json'); S1 = Fraction(d['constants']['S_1'])
    for R in (6, 8, 10, 12):
        r = d[str(R)]; lam = Fraction(r['L_R_certified']); Dlow = Fraction(r['plain']['certified_min'])
        assert lam < Dlow                                                              # Lambda_R < D_R
        assert float(Dlow) - r['eps_upper'] <= float(lam) + 1e-9                         # Lambda_R >= D_R - eps (Weyl)
        assert lam < Fraction(87649120247, 10 ** 10)                                    # below the certified upper bound
        rho = R - 311 / 175; K = (math.pi ** 2 / 6) / (1 - math.pi ** 2 * (15 / 7) ** 2 / (6 * rho ** 2))
        assert r['eps_upper'] <= K * float(S1) / rho ** 2 + 1e-9                        # eps(rho) <= K(rho) S1 / rho^2
    for v in c['K'].values():
        assert abs(v['K_upper'] - (math.pi ** 2 / 6) / (1 - math.pi ** 2 * v['eta_max'] ** 2 / 6)) < 1e-9 and v['max_on_grid'] <= v['K_upper']
        assert v['c_ge_1_minus_pi2eta2over6_on_grid']
    for name, v in c['finite_patch'].items(): assert v['holds'], name                    # IMS bound below exact lambda_min
    for R in (6, 8):                                                                       # second implementation reproduces the main one
        r = c[f'census_R{R}']; m = d[str(R)]
        assert r['distinct_balls'] == m['distinct_balls'] and abs(r['D_R_float'] - m['plain']['lambda_min_float_min']) < 1e-8
        assert abs(r['Lambda_R_float'] - m['lambda_tilde_float_min']) < 1e-6
    assert max(max(abs(x['cartesian'] - x['closed']), abs(x['radial_quad'] - x['closed'])) for x in c['overlap']) < 2e-3


# ------------------------------------------------------------------ controls
def test_matched_controls():
    d = load('phase7b_controls.json'); ims = load('phase7_ims.json'); lam12 = Fraction(ims['12']['L_R_certified'])
    for k in (1, 2, 3): assert Fraction(d[f'FR30_chi{k}']['5']['rayleigh_upper_exact']) < lam12        # FR30 > each Abelian shadow
    assert Fraction(d['Z2_reflect']['5']['rayleigh_upper_exact']) < lam12
    cc = d['crosscheck_fr30_L4']; assert abs(d['FR30']['4']['f_m1'] - cc['phase5b_f_m1']) < 1e-12 and abs(d['FR30']['4']['f_trl'] - cc['phase5b_f_trl']) < 1e-12
    for s in (1, 2): assert d[f'rand_Z2_{s}']['5']['lambda_min'] > d['FR30']['5']['lambda_min']         # finite-volume only
    sc = load('phase7b_scaling.json')
    for name in ('FR30_chi1', 'FR30_chi2', 'Z2_reflect', 'trivial'):
        assert Fraction(sc[name]['rayleigh_upper_exact']) < lam12
        assert Fraction(sc[name]['rayleigh_upper_exact']) <= Fraction(d[name]['5']['rayleigh_upper_exact'])          # L6 tighter than L5
