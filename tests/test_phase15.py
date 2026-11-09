"""Phase XV: the boundary weight of the low-energy states on the top-level interface Gamma_L (rule 1387).  The preregistration is
checked unchanged, the exact facts (|Gamma_L| = 48 * 4^L, copy blocks = H(T_L), Kramers pairing, the bracketing identity) are
rerun live at small L, and the stored exponents are recomputed from the stored values."""
import os, sys, json, hashlib
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__)); AUD = os.path.join(HERE, '..', 'audit'); RES = os.path.join(AUD, 'results')
sys.path.insert(0, AUD)
import phase11_chair as C
import phase15_boundary_weight as B

PRE = os.path.join(RES, 'phase15_preregistration_boundary_weight.json')
PRE_SHA = '30e706f08a3c9b3b4575fee1d29e132338a344e13cb4fd983d296d5f162a6e6a'      # as committed in d8adbb1 (LF line ends)
DEC = C.rule('1387')
def J(name): return json.load(open(os.path.join(RES, name), encoding='utf8'))

def test_preregistration_unchanged():
    assert hashlib.sha256(open(PRE, 'rb').read().replace(b'\r\n', b'\n')).hexdigest() == PRE_SHA

def test_rule_1387_is_extended_184323():
    assert DEC == C.extended_decoration(184323)

def test_gamma_is_a_surface_live():
    """|Gamma_L| = 48 * 4^L exactly for L = 1..3 (live) and in the stored record for L = 1..5"""
    for L in (1, 2, 3):
        *_, gam = B.geometry(DEC, L); assert gam.sum() == 48 * 4 ** L
    d = J('phase15_boundary_weight.json')
    assert {int(L): v for L, v in d['Gamma_counts'].items()} == {L: 48 * 4 ** L for L in range(1, 6)}

def test_copy_blocks_are_H_of_T_L_live():
    """the pinned operator on each of the 8 copies is the matrix of T_L itself (natural tile order), so lambda(copy) = lambda(T_L)"""
    for L in (1, 2, 3):
        G, T = C.supertile(DEC, L + 1); H = C.operators(G, T); m = 8 ** L; HL = C.operators(*C.supertile(DEC, L))
        assert all(abs(H[2 * c * m:2 * (c + 1) * m, 2 * c * m:2 * (c + 1) * m] - HL).max() == 0 for c in range(8))

def kramers(v):
    """J v = i sigma_y conj(v) tile by tile"""
    s = np.conj(v.reshape(-1, 2)); return np.stack([s[:, 1], -s[:, 0]], 1).ravel()

def test_kramers_pairing_live():
    """H commutes with the antiunitary J (J^2 = -1): every eigenvalue is doubly degenerate, and the tile density |psi_a|^2 is the same
    for every vector of a Kramers pair (psi_a and (J psi)_a are orthogonal in C^2 with equal norms)"""
    G, T = C.supertile(DEC, 3); H = C.operators(G, T)
    v = np.random.default_rng(1).standard_normal(H.shape[0]) + 1j * np.random.default_rng(2).standard_normal(H.shape[0])
    assert np.abs(H @ kramers(v) - kramers(H @ v)).max() < 1e-12 and np.allclose(kramers(kramers(v)), -v)
    w = np.linalg.eigvalsh(H.toarray()); assert np.abs(w[0::2] - w[1::2]).max() < 1e-9

def test_bracketing_identity_live():
    """H(T_{L+1}) = (sum of copy blocks) - A_Gamma; hence 0 <= lambda_L - lambda_{L+1} <= <phi_0|A_Gamma|phi_0>, and an embedded copy
    ground state has Rayleigh quotient lambda_L in T_{L+1}"""
    for L in (1, 2):
        r = B.level(DEC, L)
        assert r['bracketing']['holds'] and r['bracketing']['lambda_L_minus_lambda_L+1'] >= 0
        assert all(abs(st['rayleigh_in_T_L+1_minus_lambda']) < 1e-10 for cr in r['copies'] for st in cr['states'])
        assert all(sum(st['layer_weight']) <= 1 + 1e-12 and abs(st['layer_weight'][0] - st['w']) < 1e-12 for cr in r['copies'] for st in cr['states'])

def test_stored_record():
    d = J('phase15_boundary_weight.json'); lv = {int(L): r for L, r in d['levels'].items()}
    assert sorted(lv) == [2, 3, 4, 5]
    for L, r in lv.items():
        assert r['copy_blocks_equal_H_T_L'] and r['bracketing']['holds']
        assert abs(r['lambda_L'][0] - r['lambda_L'][1]) < 1e-8                                   # Kramers pair
        assert r['A_w_max'][0] <= r['A_g_max'][0] <= r['n_Gamma_max'] * r['A_w_max'][0] + 1e-15  # w <= g <= n_max w (psi extended by 0)
    for L in (3, 4, 5):                                                                          # A at level L = B at level L - 1
        assert abs(lv[L]['lambda_L'][0] - lv[L - 1]['lambda_L+1'][0]) < 1e-7
    for L, c in d['check_against_stored_Y'].items(): assert c['below_stored_upper']

def test_fits_recomputed():
    d = J('phase15_boundary_weight.json'); lv = {int(L): r for L, r in d['levels'].items()}; Ls = sorted(lv)
    f = B.fit(Ls, [lv[L]['A_w_max'][0] for L in Ls]); s = d['fits']['primary']
    assert abs(f['p'] - s['p']) < 1e-12 and abs(f['jackknife_se'] - s['jackknife_se']) < 1e-12
    assert s['verdict'] == B.verdict(s['p'])

def test_neumann_companion_record():
    """[E], not preregistered: the free copy states keep >= 94 % of their weight on Gamma_L and lambda_min F saturates below 6"""
    d = J('phase15_neumann_weight.json'); lv = {int(L): r for L, r in d['levels'].items()}
    assert sorted(lv) == [2, 3, 4, 5]
    assert all(r['w_Gamma_max'][0] > 0.94 and r['lambda_F'][0] < 6 for r in lv.values())
    assert abs(d['fit_w_Gamma_max_k0']['p']) < 0.05
