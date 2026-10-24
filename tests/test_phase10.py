"""Phase X tests (deliverables/PHASE10_REPORT.md): candidate construction, gauge invariance, operator assembly, certificate
verification, and consistency of the stored census, certification and laboratory results.
Run: python -m pytest -q tests/test_phase10.py"""
import os, sys, json, math, types, itertools
from fractions import Fraction
import numpy as np
import pytest
HERE = os.path.dirname(os.path.abspath(__file__)); AUD = os.path.join(HERE, '..', 'audit'); sys.path.insert(0, AUD)
sys.modules.setdefault('resource', types.SimpleNamespace(getrusage=lambda *a: types.SimpleNamespace(ru_maxrss=0), RUSAGE_SELF=0))
RES = os.path.join(AUD, 'results')
def load(n): return json.load(open(os.path.join(RES, n)))
def jsonl(n): return [json.loads(l) for l in open(os.path.join(RES, n))]
import phase9_pair as P9
import phase10_census as C


# ------------------------------------------------------------------ candidate construction
def test_gauge_classes_partition_the_census():
    cls = C.gauge_classes(); members = [i for _, m in cls for i in m]
    assert len(cls) == 1098 and sorted(members) == list(range(6561)) and all(r == min(m) for r, m in cls)
    fr = [r for r, m in cls if 4752 in m][0]; assert fr == 1386                    # FR30 = decoration 4752 lies in class 1386


def test_class_members_are_isospectral_at_level3():
    cls = dict(C.gauge_classes())
    for rep in (1386, 937, 1387):
        ev = [np.linalg.eigvalsh(P9.build([P9.decoration(i)] * 3)['H'].toarray()) for i in cls[rep][:3]]
        assert all(np.abs(e - ev[0]).max() < 1e-9 for e in ev)


# ------------------------------------------------------------------ gauge invariance and operator assembly
def test_spectrum_is_gauge_invariant():
    rng = np.random.default_rng(3); S = P9.build([P9.decoration(1387)] * 2); H = S['H'].toarray(); n = S['n']
    g = []
    for _ in range(n):
        a = rng.normal(size=4); a /= np.linalg.norm(a); g.append(np.array([[a[0] + 1j * a[3], a[2] + 1j * a[1]], [-a[2] + 1j * a[1], a[0] - 1j * a[3]]]))
    Gm = np.zeros((2 * n, 2 * n), complex)
    for i, x in enumerate(g): Gm[2 * i:2 * i + 2, 2 * i:2 * i + 2] = x
    assert np.allclose(Gm @ Gm.conj().T, np.eye(2 * n))
    assert np.abs(np.linalg.eigvalsh(Gm @ H @ Gm.conj().T) - np.linalg.eigvalsh(H)).max() < 1e-10


def test_operator_assembly_matches_census_builder():
    from independent_clifford_q8_audit import panel_edges
    from phase5a_controls import clifford_links, build_H
    from phase5b_controls import system_tiles
    for i in (1387, 4752, 0):
        tiles, _ = system_tiles(f'dec{i}', 3); n = len(tiles); _, ed = panel_edges(tiles)
        e1 = np.linalg.eigvalsh(build_H(n, ed, clifford_links(tiles, ed), np.full(n, 24.0)).toarray())
        e2 = np.linalg.eigvalsh(P9.build([P9.decoration(i)] * 3)['H'].toarray()); assert np.abs(e1 - e2).max() < 1e-9


def test_pauli_frame_links_are_abelian_in_two_dimensions():
    """in d = 2 the normals are +-e_x, +-e_y, so every link is a product of sigma_x, sigma_y: all links commute (Z4)"""
    SIG = P9.SIG; frames = [np.diag(s) @ np.eye(2, dtype=int)[list(p)] for p in itertools.permutations(range(2)) for s in itertools.product((1, -1), repeat=2)]
    L = []
    for Ma, Mb in itertools.product(frames, repeat=2):
        for j in range(2):
            ra, rb = Ma[j], Mb[j]; ka, kb = int(np.abs(ra).argmax()), int(np.abs(rb).argmax()); L.append(ra[ka] * rb[kb] * (SIG[ka] @ SIG[kb]))
    assert all(np.allclose(A @ B, B @ A) for A in L for B in L)


def test_census_phi_closure_and_frame_primitivity():
    import phase10_ims as I
    cen = {r['class']: r for r in load('phase10_census.json')['classes']}; assert len(cen) == 1098
    assert (cen[1386]['n_types1'], cen[1387]['n_types1'], cen[1389]['n_types1'], cen[1389]['n_types1_in_T5']) == (72, 90, 102, 94)
    assert all(r['n_types1'] >= r['n_types1_in_T5'] for r in cen.values()) and sum(r['n_types1'] > r['n_types1_in_T5'] for r in cen.values()) == 1086
    assert cen[937]['U1'] != cen[938]['U1']                                        # radius-1 data separate the 937/938 pair
    for c in (1386, 1387, 937, 0):
        n, k = I.frame_primitivity(P9.decoration(c)); assert k is not None


# ------------------------------------------------------------------ bracketing and certificates
def test_bracketing_on_every_class():
    rec = load('phase10_census.json')['classes']; assert len(rec) == 1098
    for r in rec:
        F = [r[f'F{k}'] for k in (1, 2, 3, 4)]; Y = [r[f'Y{k}'] for k in (1, 2, 3, 4)]
        assert all(a <= b + 1e-9 for a, b in zip(F, F[1:])) and all(a >= b - 1e-9 for a, b in zip(Y, Y[1:]))   # monotone
        assert F[-1] <= Y[-1] + 1e-9 and r['F4'] <= r['U1'] + 1e-9


def test_certified_brackets_recompute_for_fr30_and_1387():
    import phase10_certify as K
    stored = {r['class']: r for r in jsonl('phase10_certify.jsonl')}
    for cls in (1386, 1387):
        r = K.job(cls); s = stored[cls]
        # the exact Rayleigh quotient is taken at ARPACK's eigenvector, whose random start changes its last digits: both stored and
        # recomputed fractions are rigorous upper bounds, equal to 1e-10
        assert abs(r['F3_certified_lower'] - s['F3_certified_lower']) < 1e-12
        assert abs(float(Fraction(r['Y4_upper_exact'])) - float(Fraction(s['Y4_upper_exact']))) < 1e-10
        assert r['certified_lower'] < r['certified_upper']


def test_ims_reproduces_phase7_for_fr30():
    rec = [r for r in jsonl('phase10_ims.jsonl') if r['class'] == 4752]
    by = {r['R']: r for r in rec}; p7 = load('phase7_ims.json')
    for R in (6, 8):
        assert by[R]['distinct_balls'] == p7[str(R)]['distinct_balls'] and abs(by[R]['Lambda_R_certified'] - p7[str(R)]['L_R_float']) < 1e-9


def test_ims_uses_the_phi_closed_type_set():
    """the localization enumeration needs ALL legal 1-star types; the level-5 supertile alone misses some for most rules"""
    import phase10_ims as I
    for dec, n_all, n5 in ((4752, 72, 72), (1387, 90, 90), (1389, 102, 94)):
        types_, k5 = I.phi_closed_types(P9.decoration(dec)); assert (len(types_), k5) == (n_all, n5)
    balls, types_, _, rej = I.enumerate_balls(P9.decoration(4752), 6, 3); assert len(balls) == 325 and rej == 0


def test_localization_certificate_for_1387_recomputes_on_a_sample():
    """the stored R = 8 certificate of class 1387: the enumeration reproduces the ball count, and a random sample of the balls is
    re-certified at the stored mu by an independent call of the certificate (CPU LAPACK); the stored R = 14 record is complete"""
    import phase10_ims as I
    rec = {r['R']: r for r in jsonl('phase10_ims.jsonl') if r.get('class') == 1387}
    r8, r14 = rec[8], rec[14]; assert r14['all_balls_certified'] and r14['balls_failing'] == 0 and r14['distinct_balls'] == 7527
    assert r14['Lambda_R_certified'] > float(Fraction(load('phase8_chain_m5.json')['rayleigh_upper_exact']))         # E_*(1387) > E_*(FR30)
    dec = P9.decoration(1387); R = 8; rho = Fraction(R) - Fraction(311, 175); balls, types_, n5, rej = I.enumerate_balls(dec, R, 3)
    assert len(balls) == r8['distinct_balls'] == 1450 and rej == 0 and len(types_) == n5 == 90
    d2s = set()
    for G, T, _ in types_.values():
        X14 = 14 * T + 13 * G.sum(-1); a_, b_, _ = P9.panels(C.patch_ops(G, T)[2]); d2s |= set(((X14[a_] - X14[b_]) ** 2).sum(1).tolist())
    amp = {v: float(1 / I.c_overlap(math.sqrt(v) / 14 / float(rho))) for v in sorted(d2s)}; mu = Fraction(r8['mu'])
    for i in np.random.default_rng(8).choice(len(balls), 12, replace=False):
        G, T = balls[i]; low, _ = I.work_at((G, T, float(rho), amp, mu, 4 * 2 ** -53)); assert low is not None and low >= r8['Lambda_R_certified'] - 1e-9


def test_mirror_twins_of_the_top_classes():
    """stage C: the improper leaders are the top proper classes with every child frame right-multiplied by the transposition (x y)"""
    import phase10_improper as X
    def twin(j):
        return X.ext_index({k: tuple(int(np.argmax((P9.pmat(p) @ P9.pmat((1, 0, 2)))[i])) for i in range(3)) for k, p in X.dec_of(j).items()})
    for proper_class, imp in ((1387, 539311), (1389, 539291), (1391, 539288)):
        assert X.orbit_rep(twin(X.ext_index(P9.decoration(proper_class)))) == X.orbit_rep(imp)
    n, irr, per, dets = X.frame_structure(X.dec_of(539311)); assert (n, irr, per) == (48, True, 2) and set(dets) == {-1}
    twin14 = [r for r in jsonl('phase10_ims.jsonl') if r.get('extended_index') == 539311 and r['R'] == 14][-1]        # certified above FR30
    assert twin14['all_balls_certified'] and twin14['distinct_balls'] == 7527
    assert twin14['Lambda_R_certified'] > float(Fraction(load('phase8_chain_m5.json')['rayleigh_upper_exact']))


def test_prescribed_mu_certificate_matches_reference():
    import phase10_ims as I
    S = P9.build([P9.decoration(1387)] * 2); H = S['H']; lam = float(np.linalg.eigvalsh(H.toarray())[0])
    mu = Fraction(math.floor((lam - 1e-6) * 2 ** 20), 2 ** 20)
    a, b = I.cert_lower(H.toarray(), mu, 0.0), P9.certified_lower(H, mu); assert abs(a - b) < 1e-12 and max(a, b) <= lam   # LAPACK vs Phase VII column Cholesky
    assert abs(I.cert_lower_sparse(H, mu) - b) < 1e-12
    assert I.cert_lower(H.toarray(), Fraction(math.floor((lam + 1e-3) * 2 ** 20), 2 ** 20), 0.0) is None   # no certificate above the bottom


def test_dataset_leaderboard_and_benchmarks():
    rows = load('phase10_dataset.json')['rows']; assert len(rows) == 1098
    for r in rows:
        assert r['best_certified_lower'] < r['best_certified_upper'] and r['certified_lower_F3'] >= 3.788 and r['frame_primitive_power'] is not None
    fr = next(r for r in rows if r['class'] == 1386)
    assert abs(fr['best_certified_lower'] - 7.954292264597248) < 1e-12 and abs(fr['best_certified_upper'] - 8.764227038115036) < 1e-12
    lb = load('phase10_leaderboard.json'); v = [r['best_certified_lower'] for r in lb['top30']]; assert v == sorted(v, reverse=True)
    kinds = ' '.join(b['benchmark'] for b in lb['external_benchmarks'])
    assert all(w in kinds for w in ('Abelian shadow', 'scrambled', 'periodic', '937', 'Z^3'))


def test_abelian_shadows_reproduce_phase7b():
    sh = load('phase10_shadows.json')['4752']; seq = load('phase7b_scaling.json')['Y_sequences_from_L2']
    for L in (3, 4, 5):
        assert abs(sh['chi1'][f'Y{L}'] - seq['FR30_chi1'][L - 2]) < 1e-8 and abs(sh['chi2'][f'Y{L}'] - seq['FR30_chi2'][L - 2]) < 1e-8
        assert abs(sh['chi3'][f'Y{L}'] - sh['chi1'][f'Y{L}']) < 1e-8                  # chi_3 = chi_1 for FR30 (x <-> z mirror)


def test_periodic_approximants_respect_bracketing():
    cls_of = {i: r for r in load('phase10_census.json')['classes'] for i in r['members']}
    for r in jsonl('phase10_periodic.jsonl'): assert r['E_per'] >= cls_of[r['class']][f"F{r['k']}"] - 1e-9


def test_registered_stage_b_selection_reproduces():
    cen = {r['class']: r for r in load('phase10_census.json')['classes']}; sel = load('phase10_stageB_selection.json')
    chosen = sorted(cen, key=lambda c: -cen[c]['Y4'])[:15]
    chosen += [c for c in sorted(cen, key=lambda c: -cen[c]['F4']) if c not in chosen][:5]
    assert sel['selected'] == chosen and sel['benchmarks'] == [1386, 937, 938]
    assert sel['random_sample_200'] == sorted(int(x) for x in np.random.default_rng(20261024).choice(sorted(cen), size=200, replace=False))


# ------------------------------------------------------------------ stage C: improper frames
def test_improper_extension_space_and_batched_operator():
    import phase10_improper as X
    D = np.array([(np.arange(X.N8) // 6 ** c) % 6 for c in range(8)]); sgn = np.array([P9.psign(p) for p in X.PERMS])
    par = np.array([1] + [1 if sum(v) % 2 == 0 else -1 for v in P9.U3]); assert (sgn[D] == par[:, None]).all(0).sum() == 3 ** 8
    bt = X.Batched(2); js = np.random.default_rng(2).integers(0, X.N8, 5)
    for j, v in zip(js, bt.bottoms(js)): assert abs(np.linalg.eigvalsh(P9.build([X.dec_of(int(j))] * 2)['H'].toarray())[0] - v) < 1e-9
    cen = {r['class']: r for r in load('phase10_census.json')['classes']}; cls_of = {i: r['class'] for r in cen.values() for i in r['members']}
    proper = [j for j in range(0, X.N8, 4999) if X.is_proper(j)][:4]
    for j, v in zip(proper, bt.bottoms(np.array(proper))): assert abs(v - cen[cls_of[X.census_index(j)]]['Y2']) < 1e-9


# ------------------------------------------------------------------ second geometry
def test_z3_bloch_operator_and_flatness():
    import phase10_z3 as Z
    F = np.array([Z.PROPER[5]] * 27).reshape(3, 3, 3, 3, 3); c = Z.Cell(F)
    assert abs(c.floor(grid=4)[0]) < 1e-9 and Z.counts(c.plaquettes()) == (81, 0, 0)        # constant frames: flat, E = 0
    rng = np.random.default_rng(5); c = Z.Cell(Z.random_cell(rng, 3)); th = np.array([0.4, 1.3, 2.9]); H = c.bloch(th)
    assert np.allclose(H, H.conj().T)
    Hp, Hf = c.cell_ops(); E = c.floor(grid=4)[0]
    assert np.linalg.eigvalsh(Hf)[0] <= E + 1e-9 <= np.linalg.eigvalsh(Hp)[0] + 1e-9               # bracketing on Z^3


def test_z3_no_go_family():
    rows = load('phase10_z3_noflat.json')['rows']
    for r in rows:
        assert r['nontrivial_plaquette_fraction'] > 0.75 and abs(r['rayleigh_upper_on_E'] - r['bound_6sin2']) < 1e-9
    assert rows[-1]['rayleigh_upper_on_E'] < 0.37


def test_z3_trace_matched_pair_certificate_recomputes():
    """Theorem X.5: identical plaquette trace fields, E_*(A) <= exact Rayleigh < certified free-cell bound <= E_*(B)"""
    import phase10_z3 as Z, scipy.sparse as sp
    d = load('phase10_z3_pairs.json'); b, v = d['best'], d['certificate_v2']
    A, B = (Z.Cell(np.array(b[k]).reshape(2, 2, 2, 3, 3)) for k in ('frames_low', 'frames_high'))
    q = Z.exact_rayleigh_dense(A.bloch(np.zeros(3))); assert f'{q.numerator}/{q.denominator}' == v['E_low_upper_exact']
    _, Hf = B.cell_ops(); f = float(np.linalg.eigvalsh(Hf)[0]); mu = Fraction(math.floor((f - 1e-7) * 2 ** 20), 2 ** 20)
    low = P9.certified_lower(sp.csr_matrix(Hf), mu); assert abs(low - v['E_high_lower_free_cell']) < 1e-12 and low - float(q) > 0.18
    pa, pb = A.plaquettes(), B.plaquettes(); assert Z.trace_field(pa) == Z.trace_field(pb) and Z.counts(pa) == Z.counts(pb) and pa != pb


def test_z3_class_field_matched_pair_certificate_recomputes():
    """Theorem X.5 (strong form): identical Q8 class on every plaquette, gauge-equivalent Abelian shadows, certified different floors"""
    import phase10_z3 as Z, scipy.sparse as sp
    d = load('phase10_z3_classpairs.json'); b, v = d['best'], d['certificate']
    A, B = (Z.Cell(np.array(b[k]).reshape(2, 2, 2, 3, 3)) for k in ('frames_low', 'frames_high'))
    assert A.plaquettes() == B.plaquettes() and not np.array_equal(A.F, B.F)
    q = Z.exact_rayleigh_dense(A.bloch(np.zeros(3))); assert f'{q.numerator}/{q.denominator}' == v['E_low_upper_exact']
    _, Hf = B.cell_ops(); f = float(np.linalg.eigvalsh(Hf)[0]); mu = Fraction(math.floor((f - 1e-7) * 2 ** 20), 2 ** 20)
    assert P9.certified_lower(sp.csr_matrix(Hf), mu) - float(q) > 0.18
    for k in range(3): assert abs(Z.Shadow(A, k).floor(grid=4)[0] - Z.Shadow(B, k).floor(grid=4)[0]) < 1e-9
