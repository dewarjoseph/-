"""Phase VIII tests (deliverables/PHASE8_REPORT.md).  Fast tests recompute structural statements; JSON tests check the stored
outputs of the long runs for internal consistency (they are not independent proofs).
Run: python -m pytest -q tests/test_phase8.py"""
import os, sys, json, types
import numpy as np
import pytest
HERE = os.path.dirname(os.path.abspath(__file__)); AUD = os.path.join(HERE, '..', 'audit'); sys.path.insert(0, AUD)
sys.modules.setdefault('resource', types.SimpleNamespace(getrusage=lambda *a: types.SimpleNamespace(ru_maxrss=0), RUSAGE_SELF=0))
RES = os.path.join(AUD, 'results')
def load(n): return json.load(open(os.path.join(RES, n)))


# ------------------------------------------------------------------ section 2: the exact interface recursion
def _parent_response(E, Rs, level=3):
    """R_{m+1}(E) from eight child responses via the glued operator (V-D Glued) and a Schur complement onto the outer surface."""
    import phase5d_schur as d
    from independent_clifford_q8_audit import FR30
    tiles = d.tiles_of(FR30, level); H, edges = d.build(tiles); n = len(tiles); child, surf = d.partition(n, edges, level)
    G = d.Glued(H, child, surf); K = G.K(E, Rs) if Rs is not None else G.K(E)
    deg = d.degrees(n, edges); outer = deg[G.Sall] < 24                      # positions of S (children surfaces) on the parent surface
    so, sj = np.nonzero(np.repeat(outer, 2))[0], np.nonzero(~np.repeat(outer, 2))[0]
    return K[np.ix_(so, so)] - K[np.ix_(so, sj)] @ np.linalg.solve(K[np.ix_(sj, sj)], K[np.ix_(sj, so)]), G, H, deg

def test_recursion_exact_monotone_concave():
    import phase5d_schur as d
    E = 7.0; Rpar, G, H, deg = _parent_response(E, None)
    S = np.nonzero(deg < 24)[0]; I = np.nonzero(deg == 24)[0]; ss, ii = d.spinor(S), d.spinor(I); Hd = H.toarray()
    direct = Hd[np.ix_(ss, ss)] - E * np.eye(len(ss)) - Hd[np.ix_(ss, ii)] @ np.linalg.solve(Hd[np.ix_(ii, ii)] - E * np.eye(len(ii)), Hd[np.ix_(ii, ss)])
    # the recursion lists the parent surface in the order of the children's surfaces; compare as sets of entries via sorting by tile
    order = np.argsort(np.repeat(G.Sall[deg[G.Sall] < 24], 2) * 2 + np.tile([0, 1], (deg[G.Sall] < 24).sum()))
    assert np.allclose(Rpar[np.ix_(order, order)], direct, atol=1e-9)            # exactness (Theorem D2)
    rng = np.random.default_rng(0); Rs = G.R(E)
    Ds = []
    for R in Rs:
        X = rng.standard_normal(R.shape) + 1j * rng.standard_normal(R.shape); Ds.append(0.01 * X @ X.conj().T)
    Rup, *_ = _parent_response(E, [R + D for R, D in zip(Rs, Ds)])
    assert np.linalg.eigvalsh(Rup - Rpar).min() > -1e-9                          # Loewner monotone (Prop. 8.1b)
    Rmid, *_ = _parent_response(E, [R + 0.5 * D for R, D in zip(Rs, Ds)])
    assert np.linalg.eigvalsh(Rmid - 0.5 * (Rpar + Rup)).min() > -1e-9           # concave


def test_surface_counts():
    import phase7_local as P
    want = [8, 53, 287, 1331, 5723]
    for m, w in zip(range(1, 6), want):
        G, T = P.gen_poses(m); grid = P.owner_grid(m, G, T); n = len(G); surf = np.zeros(n, bool)
        for ax in range(3):
            for sgn in (1, -1):
                sh = np.roll(grid, -sgn, axis=ax); idx = [slice(None)] * 3; idx[ax] = -1 if sgn == 1 else 0; sh[tuple(idx)] = -1
                surf[np.unique(grid[(grid >= 0) & (sh < 0)])] = True
        assert surf.sum() == w


# ------------------------------------------------------------------ sections 3/5: environment patches and the selection chain
def test_patch_central_copy_is_the_supertile():
    import phase7_local as P
    import phase5d_schur as d
    from independent_clifford_q8_audit import FR30
    from phase8_env_fiber import patch_operator
    from phase8_patch_bounds import types_sorted
    tau = types_sorted()[59]; poses, c = P.poses_from_key(tau)
    for _ in range(2): poses = P.inflate(poses)
    H = patch_operator(poses).toarray(); blk = np.arange(2 * c * 64, 2 * (c + 1) * 64)
    H2, _ = d.build(d.tiles_of(FR30, 2)); assert np.allclose(H[np.ix_(blk, blk)], H2.toarray())


def test_every_patch_copy_is_the_supertile():
    """Theorem 8.2's premise: sigma^m(tau) is a union of |tau| copies of T_m, each carrying T_m's operator in canonical order,
    so U_m(tau) is a functional of R_m alone (with Theorem E1 for the partition into copies)."""
    import phase7_local as P
    import phase5d_schur as d
    from independent_clifford_q8_audit import FR30
    from phase8_env_fiber import patch_operator
    from phase8_patch_bounds import types_sorted
    tau = types_sorted()[59]; poses, c = P.poses_from_key(tau)
    for _ in range(2): poses = P.inflate(poses)
    H = patch_operator(poses).tocsr(); H2 = d.build(d.tiles_of(FR30, 2))[0].toarray()
    for j in range(len(tau)):
        blk = np.arange(2 * j * 64, 2 * (j + 1) * 64); assert np.allclose(H[blk][:, blk].toarray(), H2)


def test_selection_chain_is_a_self_loop_and_monotone():
    import phase7_local as P
    from phase8_patch_bounds import types_sorted
    T = types_sorted(); idx = {t: i for i, t in enumerate(T)}
    assert [idx[k] for k in P.Phi_r(T[59], P.LODD[1])][5] == 59 and [idx[k] for k in P.Phi_r(T[63], P.LODD[1])][2] == 63
    pb = load('phase8_patch_bounds.json'); u = [pb['U'][str(m)]['per_type']['59'] for m in sorted(map(int, pb['U']))]
    assert all(a >= b - 1e-10 for a, b in zip(u, u[1:]))                          # nested patches: non-increasing
    assert all(pb['U'][m]['argmin'][0] in (35, 39, 59, 63) for m in pb['U'])          # the selecting set (ties within 1e-9 at m = 4)
    assert all(abs(pb['U'][m]['per_type']['59'] - pb['U'][m]['min']) < 1e-6 for m in pb['U'])
    assert min(u) > 7.954292                                                      # above the certified lower bound (Phase VII)


# ------------------------------------------------------------------ section 7: counterexample to conjugacy-class sufficiency
def test_class_count_counterexample():
    import phase5b_sweep as sw
    from phase5b_controls import system_tiles
    from independent_clifford_q8_audit import panel_edges
    from phase5a_controls import clifford_links, build_H
    keys, bots = [], []
    for r in (937, 938):
        tiles4, _ = system_tiles(f'dec{r}', 4); p = sw.predictors(tiles4, 4)
        keys.append((p['n_plus'], p['n_minus'], p['n_i'], p['n_j'], p['n_k']))
        tiles3, _ = system_tiles(f'dec{r}', 3); n = len(tiles3); _, ed = panel_edges(tiles3)
        H = build_H(n, ed, clifford_links(tiles3, ed), np.full(n, 24.0)).toarray(); bots.append(np.linalg.eigvalsh(H)[0])
    assert sorted(keys[0][2:]) == sorted(keys[1][2:]) and keys[0][:2] == keys[1][:2]   # identical level-4 class counts
    assert abs(bots[0] - bots[1]) > 0.27                                          # different level-3 bottoms


def test_class_count_census_has_one_collision():
    """In the 6561-rule census the level-4 class-count vector (n+, n-, sorted n_i, n_j, n_k) has exactly one value shared by rules
    with different level-3 bottoms, and it contains 937/938 (recomputed from the census records)."""
    import collections
    R = load('phase5b_sweep.json')['records']; g = collections.defaultdict(set)
    for r in R:
        p = r['pred']; g[(p['n_plus'], p['n_minus'], tuple(sorted((p['n_i'], p['n_j'], p['n_k']))))].add((r['index'], round(r['L3']['lambda'][0], 7)))
    multi = [v for v in g.values() if len({e for _, e in v}) > 1]
    assert len(R) == 6561 and len(g) == 1097 and len(multi) == 1 and {937, 938} <= {i for i, _ in multi[0]}
    cp = load('phase8_classpair.json'); assert cp['groups_with_distinct_bottoms'] == 1 and len(cp['groups'][0]['identical_statistics']) == 28


def test_control_legality():
    lg = load('phase8_legality.json')
    assert lg['fr30']['illegal'] == 0 and lg['fr30']['distinct_types'] == 72
    assert all(v['illegal_fraction'] > 0.67 for k, v in lg.items() if k != 'fr30')


# ------------------------------------------------------------------ Lean <-> Python: the Q8 table and the shadow characters
def test_lean_shadow_table_matches_python():
    """certificates/Phase8Shadows.lean's umul/chi (transcribed) agree with phase7_adversarial.MUL (index 2*unit + sign), and
    hence with the explicit Pauli matrices that test_phase7b checks MUL against; chi_k as used in phase7b_controls agrees."""
    import phase7_adversarial as A
    from phase7b_controls import CHI
    tab = {(0, 'x'): None}
    def umul(a, b):
        if a == 0: return (b, False)
        if b == 0: return (a, False)
        if a == b: return (0, True)
        return {(1, 2): (3, False), (2, 3): (1, False), (3, 1): (2, False), (2, 1): (3, True), (3, 2): (1, True), (1, 3): (2, True)}[(a, b)]
    for x in range(8):
        for y in range(8):
            u, s = umul(x // 2, y // 2); lean = 2 * u + int((x % 2) ^ (y % 2) ^ int(s))
            assert lean == A.MUL[x, y]
    for k in (1, 2, 3):
        for x in range(8): assert CHI[k][x] == (1 if (x // 2) in (0, k) else -1)
    src = open(os.path.join(HERE, '..', 'certificates', 'Phase8Shadows.lean'), encoding='utf-8').read()
    assert 'sorry' not in src and 'native_decide' not in src and 'theorem chi_hom' in src


# ------------------------------------------------------------------ stored long-run results
def test_chain_m5_certificate():
    from fractions import Fraction
    c = load('phase8_chain_m5.json'); q = Fraction(c['rayleigh_upper_exact'])
    assert c['type'] == 59 and c['m'] == 5 and c['residual'] < 1e-8
    assert q >= Fraction(c['lambda_float']) - Fraction(1, 10 ** 9)                    # Rayleigh quotient of an approximate eigenvector
    assert q < Fraction(87649120247, 10 ** 10)                                        # improves V-E's certified upper bound
    pb = load('phase8_patch_bounds.json'); assert c['lambda_float'] < pb['U']['4']['per_type']['59']   # chain still decreasing


def test_fiber_and_copy_rg_results():
    ef = load('phase8_env_fiber.json')
    assert ef['capture']['7']['env']['58'] > 0.997 and ef['capture']['6']['env']['58'] > 0.996
    rows = [json.loads(l) for l in open(os.path.join(RES, 'phase8_copy_rg.jsonl'))]
    for r in rows:
        if r['err'] is not None: assert r['err'] > -1e-9                         # Ritz: E_W >= exact edge (Theorem E3)
    v = {(r['L'], r['fiber'], r['d']): r['err'] for r in rows}
    assert abs(v[(5, 'deep67', 58)] - 0.01945) < 1e-4                           # reproduces V-E closure5


def test_copy_rg_block_operator_reproduces_stored_edge():
    """the block-sparse solver (BSR coupling, I (x) m(E) applied as a LinearOperator) reproduces the first stored level-5 edge"""
    import phase8_copy_rg as C
    rows = [json.loads(l) for l in open(os.path.join(RES, 'phase8_copy_rg.jsonl'))]
    ref = next(r['err'] for r in rows if (r['L'], r['fiber'], r['d']) == (5, 'env', 58))
    assert abs(C.solve(5, 58, 'env', write=False)['err'] - ref) < 1e-9
