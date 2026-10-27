"""Phase XIII: the reconstruction of the counting algorithm of "The Exponential Time Hypothesis is False" (openai/math, Family 378)
and its concrete cost audit.  Fast checks recompute small instances live; the stored battery is checked for consistency."""
import os, sys, json, math, random
from fractions import Fraction
import pytest
HERE = os.path.dirname(os.path.abspath(__file__)); AUD = os.path.join(HERE, '..', 'audit'); RES = os.path.join(AUD, 'results')
sys.path.insert(0, AUD)
import phase13_eth as E
import phase13_eth_costs as K

def J(name): return json.load(open(os.path.join(RES, name)))

def test_remark_4_4_live():
    """the paper's worked example: M_0 = Pi_1 + Pi_2 - Pi_1 Pi_2 and the row zeta_0 - (T/2) zeta_1 - T zeta_2"""
    rep = E.check_remark_4_4(); assert rep['row_matches'] and rep['M0_is_Pi1+Pi2-Pi1Pi2']

def test_lemmas_4_1_to_4_3_live():
    rep = E.check_aux(E.Aux(2, 3, 2), slow=True)
    keys = ['f_interpolates', 'g_vanishes_above_R-1', 'lemma_4_2_support', 'eigen_relation', 'lemma_4_1_fixes_I_directions',
            'orthogonal_sample', 'c_B_matches', 'lemma_4_3_P0', 'lemma_4_3_degree', 'lemma_4_3_kernel', 'lemma_4_6_denominator',
            'M0_expansion_equals_matrix_product']
    assert all(rep[k] for k in keys), {k: rep[k] for k in keys}
    assert rep['c_B'] == 10                       # 64 * Pr[Bin(3, 1/4) >= 2] = 64 * 10/64

def test_count_exact_over_Q_live():
    """the full routine (Lemmas 3.2, 3.3, Hermite interpolation) returns the brute-force count, exactly over Q"""
    rep = E.check_count(2, 3, 2, 4, 2, 11, modular=False)
    assert rep['equal'] and rep['jets_equal_direct'] and rep['H_degree_le_dH'] and rep['count_algorithm'] == 12

def test_count_truncated_regime_live():
    """q < n: the Taylor data use only |E| <= q, and the count is still exact"""
    rep = E.check_count(2, 4, 2, 6, 3, 13, modular=True)
    assert rep['q'] < rep['n'] and rep['equal'] and rep['jets_equal_direct']

def test_adversarial_live():
    """removing one essential measurement row breaks Definition 3.1(4) and the separated sum"""
    rep = E.check_adversarial(2, 3, 2, 6, 4, 21)
    assert rep['separated_equals_direct']
    assert not rep['all_rows_removed']['kernel_condition_holds'] and not rep['all_rows_removed']['separated_equals_direct']
    one = rep['one_essential_row_removed']
    assert isinstance(one, dict) and not one['kernel_condition_holds'] and not one['separated_equals_direct']

def test_stored_battery():
    d = J('phase13_eth.json')
    assert d['remark_4_4']['row_matches']
    for rep in d['aux']:
        assert rep['c_B_matches'] and rep['lemma_4_1_fixes_I_directions'] and rep['lemma_4_2_support'] and rep['lemma_4_3_kernel']
    for rep in d['layout']: assert rep['P0_is_delta'] and rep['kernel_condition'] and rep['row_sum_le_D']
    assert len(d['count']) >= 8 and all(r['equal'] and r['jets_equal_direct'] for r in d['count'])
    assert any(r['q'] < r['n'] for r in d['count']) and sum(r['field'] == 'Q' for r in d['count']) >= 2
    for rep in d['adversarial']:
        assert rep['separated_equals_direct'] and not rep['one_essential_row_removed']['separated_equals_direct']

def test_explicit_schedule_threshold():
    """Lemma 4.8's integer guards (r >= 2, Q > R, R >= 32, 6R <= Q) first pass at lambda = ceil(log2 n) = 10 909 384 704"""
    lam = K.least_lambda(1); assert lam == 10909384704 and K.guards(lam) and not K.guards(lam - 1)
    nu, r, Q, R = K.explicit(lam); assert (nu, r, Q, R) == (34, 90, 2506752, 417792) and 6 * R <= Q < 6 * R + 6
    d = J('phase13_eth_costs.json'); assert d['explicit_schedule']['1']['least_lambda'] == lam

def test_lean_goodinput_threshold():
    """GoodInput n := 32 <= log2(log2 n) (Nat.log2 = floor) holds exactly from n = 2^(2^32)"""
    def good(floor_log2_n): return 32 <= floor_log2_n.bit_length() - 1      # Nat.log2 m = m.bit_length() - 1
    # n = 2^(2^32) has floor(log2 n) = 2^32; n = 2^(2^32) - 1 has floor(log2 n) = 2^32 - 1 (the integers themselves need 512 MB)
    assert good(2 ** 32) and not good(2 ** 32 - 1)

def test_free_search_record():
    d = J('phase13_eth_costs.json')['free_search']['1']
    assert d['rate_with_exact_tail'] < 1 and d['log2_n_min'] > 15000
    t = K.exact_tail(d['Q'], d['r'], d['A0'], d['R']); assert abs(float(t) - d['tail_exact_float']) < 1e-20
