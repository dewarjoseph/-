"""
phase5a_referee_links_check.py -- hostile-referee re-derivation of the level-1/level-2 shared-panel link statistics
claimed by audit/phase5a_independent_enumerator.py (agent A1):
    level 1: 48 shared unit panels, link values +1:6, -1:24, traceless:18
    level 2: 576 shared unit panels, link values +1:90, -1:228, traceless:258
    on every panel (sigma.u_a)(sigma.u_b) == matrix of -(u_a u_b) under e_i = -i sigma_i.

Three code paths are run and compared:
  (R) the referee's own from-scratch implementation written in this session: numpy 3x3 integer matrices for the
      poses, 2x2 Pauli matrices for the links, Hamilton product on 4-vectors for the quaternion side.  It shares
      only the documented axioms (A1 prototile, A2 inflation rule, A3 FR30 data, A5 link rule) with the repository.
  (P) the repository's primitives in audit/independent_clifford_q8_audit.py (tiles_at_level, panel_edges,
      clifford_link, q8label), loaded with importlib.
  (A) A1's module audit/phase5a_independent_enumerator.py loaded with importlib and run in-process
      (Level.panels_and_pauli_check, pauli_identity_check); its output files are NOT rewritten.
Discriminating-power tests: wrong embedding e_i = +i sigma_i must break the identity on traceless panels; changing the
decoration (frame rule) must change the value counts; orientation / normal-sign independence of the value classes.

Run from the repository root:  python3 -u -I audit/phase5a_referee_links_check.py
Output: audit/results/phase5a_referee_links_check.{txt,json}
"""
import os, sys, json, itertools, collections, importlib.util, types, time
import numpy as np

ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
OUT = os.path.join(ROOT, 'audit', 'results')
LINES = []
def say(s=''):
    print(s, flush=True); LINES.append(s)

# ============================ (R) referee implementation ============================
U3 = [v for v in itertools.product((0, 1), repeat=3) if v != (1, 1, 1)]
FR30 = {(0, 0, 0): (0, 1, 2), (0, 0, 1): (0, 2, 1), (0, 1, 0): (2, 1, 0), (0, 1, 1): (1, 2, 0),
        (1, 0, 0): (1, 0, 2), (1, 0, 1): (0, 1, 2), (1, 1, 0): (2, 0, 1)}

def Pmat(p):
    """P[i, p[i]] = 1 (axiom A3 convention)."""
    M = np.zeros((3, 3), dtype=np.int64)
    for i in range(3): M[i, p[i]] = 1
    return M

def ref_tiles(level, rule):
    """Axiom A2 in doubled coordinates: centre child (G P(id), 2T + G(1,1,1)); octant children
    (G D_s(v) P(pi_v), 2T + 4 G v); cube corners (G(2u+1) + 2T - 1)/2."""
    I3 = np.eye(3, dtype=np.int64)
    poses = [(I3, np.zeros(3, dtype=np.int64))]
    for _ in range(level):
        nxt = []
        for G, T in poses:
            nxt.append((G @ Pmat((0, 1, 2)), 2 * T + G @ np.array([1, 1, 1])))
            for v in U3:
                Ds = np.diag([1 - 2 * v[0], 1 - 2 * v[1], 1 - 2 * v[2]]).astype(np.int64)
                nxt.append((G @ Ds @ Pmat(rule[v]), 2 * T + 4 * (G @ np.array(v))))
        poses = nxt
    tiles = []
    for G, T in poses:
        cubes = []
        for u in U3:
            num = G @ np.array([2 * u[0] + 1, 2 * u[1] + 1, 2 * u[2] + 1]) + 2 * T - 1
            assert (num % 2 == 0).all()
            cubes.append(tuple(int(x) for x in num // 2))
        tiles.append((G, T, cubes))
    return tiles

SIG = [np.array([[0, 1], [1, 0]], complex), np.array([[0, -1j], [1j, 0]], complex), np.array([[1, 0], [0, -1]], complex)]
I2 = np.eye(2, dtype=complex)
Q8_MATS = [('+1', I2), ('-1', -I2)] + [(f'{s}i*sigma{m+1}', s_ * 1j * SIG[m]) for m in range(3) for s, s_ in (('+', 1), ('-', -1))]

def sdot(u): return u[0] * SIG[0] + u[1] * SIG[1] + u[2] * SIG[2]

def hamilton(p, q):
    """Hamilton product of 4-vectors (w,x,y,z) -- the standard closed formula, not a lookup table."""
    w1, x1, y1, z1 = p; w2, x2, y2, z2 = q
    return (w1 * w2 - x1 * x2 - y1 * y2 - z1 * z2,
            w1 * x2 + x1 * w2 + y1 * z2 - z1 * y2,
            w1 * y2 - x1 * z2 + y1 * w2 + z1 * x2,
            w1 * z2 + x1 * y2 - y1 * x2 + z1 * w2)

def quat_to_su2(q, sgn):
    """e_1,e_2,e_3 -> sgn * i*sigma_1, sgn * i*sigma_2, sgn * i*sigma_3  (sgn=-1 is the documented convention)."""
    w, x, y, z = q
    return w * I2 + sgn * 1j * (x * SIG[0] + y * SIG[1] + z * SIG[2])

def classify(C):
    for name, M in Q8_MATS:
        if np.allclose(C, M, atol=1e-9):
            return name
    return 'other'

def value_class(name):
    return name if name in ('+1', '-1') else ('traceless' if name != 'other' else 'other')

def ref_owner_and_panels(tiles):
    owner = {}
    for a, (G, T, cs) in enumerate(tiles):
        for c in cs:
            assert c not in owner, 'overlap'
            owner[c] = a
    panels = []       # one entry per shared unit face, normal +e_ax from cube c (owner a) to cube c+e_ax (owner b)
    internal_faces = 0
    for c, a in owner.items():
        for ax in range(3):
            c2 = list(c); c2[ax] += 1; c2 = tuple(c2)
            b = owner.get(c2)
            if b is None: continue
            internal_faces += 1
            if b != a: panels.append((a, b, ax, c, c2))
    return owner, panels, internal_faces

def ref_level(level, rule, label):
    t0 = time.time()
    tiles = ref_tiles(level, rule)
    owner, panels, internal_faces = ref_owner_and_panels(tiles)
    N = 2 ** (level + 1)
    target = {c for c in itertools.product(range(N), repeat=3) if not all(x >= N // 2 for x in c)}
    fills = (set(owner) == target)
    dets = sorted({int(round(np.linalg.det(G))) for G, _, _ in tiles})
    vals = collections.Counter(); names = collections.Counter()
    id_ok_minus = 0; id_ok_plus = 0; orient_ok = True; nsign_ok = True; in_q8 = True
    pairs_seen = set()
    for (a, b, ax, c, c2) in panels:
        n = np.zeros(3, dtype=np.int64); n[ax] = 1
        ua = tiles[a][0].T @ n; ub = tiles[b][0].T @ n
        C = sdot(ua) @ sdot(ub)
        name = classify(C); names[name] += 1; vals[value_class(name)] += 1
        in_q8 &= (name != 'other')
        qa = (0, *[int(x) for x in ua]); qb = (0, *[int(x) for x in ub])
        q = tuple(-x for x in hamilton(qa, qb))         # -(u_a u_b)
        id_ok_minus += int(np.allclose(C, quat_to_su2(q, -1)))
        id_ok_plus += int(np.allclose(C, quat_to_su2(q, +1)))
        # orientation (a<->b) and normal sign (n -> -n) independence of the value class
        orient_ok &= (value_class(classify(sdot(ub) @ sdot(ua))) == value_class(name))
        nsign_ok &= (value_class(classify(sdot(-ua) @ sdot(-ub))) == value_class(name))
        pairs_seen.add((tuple(int(x) for x in ua), tuple(int(x) for x in ub)))
    intra = 9 * len(tiles)   # chair prototile: 12 internal faces of 2x2x2 minus 3 at the removed corner
    res = {'label': label, 'level': level, 'tiles': len(tiles), 'cubes': len(owner), 'fills_chair_exactly': fills,
           'frame_dets': dets, 'internal_faces': internal_faces, 'intra_tile_faces': intra,
           'shared_panels': len(panels), 'shared_panels_from_face_count': internal_faces - intra,
           'link_values': {'+1': vals['+1'], '-1': vals['-1'], 'traceless': vals['traceless'], 'other': vals['other']},
           'link_elements': dict(sorted(names.items())), 'all_links_in_Q8': bool(in_q8),
           'identity_minus_i_sigma_holds_on_panels': id_ok_minus, 'identity_plus_i_sigma_holds_on_panels': id_ok_plus,
           'value_class_orientation_independent': bool(orient_ok), 'value_class_normal_sign_independent': bool(nsign_ok),
           'distinct_(u_a,u_b)_pairs_on_panels': len(pairs_seen), 'time_s': round(time.time() - t0, 2)}
    return res, tiles

# ============================ main ============================
def main():
    report = {'script': 'audit/phase5a_referee_links_check.py'}
    say('phase5a referee check of A1 panel/link claims (three code paths)')
    say(f' numpy {np.__version__}, python {sys.version.split()[0]}')

    # -------- (R) --------
    say('\n(R) REFEREE FROM-SCRATCH IMPLEMENTATION')
    R = {}
    for lvl in (1, 2):
        res, tiles = ref_level(lvl, FR30, 'FR30'); R[lvl] = res
        say(f' level {lvl}: tiles={res["tiles"]} cubes={res["cubes"]} fills_chair={res["fills_chair_exactly"]} dets={res["frame_dets"]}')
        say(f'   internal faces={res["internal_faces"]} intra-tile faces={res["intra_tile_faces"]} -> shared panels={res["shared_panels"]} '
            f'(face-count formula {res["shared_panels_from_face_count"]})')
        say(f'   link values={res["link_values"]}  elements={res["link_elements"]}  all in Q8={res["all_links_in_Q8"]}')
        say(f'   (sigma.u_a)(sigma.u_b) == -(u_a u_b) under e_i=-i sigma_i on {res["identity_minus_i_sigma_holds_on_panels"]}/{res["shared_panels"]} panels; '
            f'under e_i=+i sigma_i on {res["identity_plus_i_sigma_holds_on_panels"]}/{res["shared_panels"]} panels')
        say(f'   value class independent of orientation={res["value_class_orientation_independent"]} and of normal sign={res["value_class_normal_sign_independent"]}; '
            f'distinct (u_a,u_b) pairs occurring={res["distinct_(u_a,u_b)_pairs_on_panels"]} (of 36)')
        if lvl == 1:
            # frames as (perm, signs) with G e_j = signs[j] e_{perm[j]}  (A1's convention) for comparison with A1's JSON
            fr = []
            for G, T, _ in tiles:
                perm = [int(np.nonzero(G[:, j])[0][0]) for j in range(3)]
                signs = [int(G[perm[j], j]) for j in range(3)]
                fr.append({'perm': perm, 'signs': signs, 'T': [int(x) for x in T]})
            R['level1_frames'] = fr
    report['R'] = R

    # 36-pair identity with the referee's Hamilton product
    ok36 = 0; bad36_plus = 0
    for ax, sx, ay, sy in itertools.product(range(3), (1, -1), range(3), (1, -1)):
        ua = np.zeros(3, int); ua[ax] = sx; ub = np.zeros(3, int); ub[ay] = sy
        C = sdot(ua) @ sdot(ub); q = tuple(-x for x in hamilton((0, *ua), (0, *ub)))
        ok36 += int(np.allclose(C, quat_to_su2(q, -1))); bad36_plus += int(not np.allclose(C, quat_to_su2(q, +1)))
    # homomorphism of the e_i -> -i sigma_i embedding on all 64 products of Q8 = {+-1, +-e1, +-e2, +-e3}
    Q8V = [(s, 0, 0, 0) for s in (1, -1)] + [tuple(s * np.eye(4, dtype=int)[m]) for m in (1, 2, 3) for s in (1, -1)]
    hom = sum(int(np.allclose(quat_to_su2(a, -1) @ quat_to_su2(b, -1), quat_to_su2(hamilton(a, b), -1))) for a in Q8V for b in Q8V)
    antihom = sum(int(np.allclose(quat_to_su2(a, +1) @ quat_to_su2(b, +1), quat_to_su2(hamilton(a, b), +1))) for a in Q8V for b in Q8V)
    report['R']['identity_36_pairs_minus'] = ok36; report['R']['identity_36_pairs_plus_fails'] = bad36_plus
    report['R']['homomorphism_64_minus'] = hom; report['R']['homomorphism_64_plus'] = antihom
    say(f' 36 signed-axis pairs: identity holds under e_i=-i sigma_i on {ok36}/36; fails under e_i=+i sigma_i on {bad36_plus}/36')
    say(f' e_i -> -i sigma_i is a homomorphism on {hom}/64 Q8 products; e_i -> +i sigma_i on {antihom}/64 (expected 64 and <64)')

    # -------- (R) perturbations: are the value counts decoration-dependent? --------
    say('\n(R) PERTURBATION CONTROLS (same point set; the numbers below must differ from FR30 for the counts to be informative)')
    def modified(**kw):
        d = dict(FR30)
        for k, v in kw.items(): d[tuple(int(ch) for ch in k[1:])] = v
        return d
    perturbs = {
        'all_identity_perms': {v: (0, 1, 2) for v in U3},
        'swap_two_3cycles_(011)<->(110)': modified(v011=(2, 0, 1), v110=(1, 2, 0)),
        'one_odd_perm_(001)->(102)': modified(v001=(1, 0, 2)),
    }
    report['R_perturbations'] = {}
    for name, rule in perturbs.items():
        report['R_perturbations'][name] = {}
        for lvl in (1, 2):
            res, _ = ref_level(lvl, rule, name); report['R_perturbations'][name][lvl] = res
            say(f' {name:34s} level {lvl}: fills_chair={res["fills_chair_exactly"]} dets={res["frame_dets"]} panels={res["shared_panels"]} '
                f'values={res["link_values"]} same_as_FR30={res["link_values"] == R[lvl]["link_values"]}')

    # -------- (P) repository primitives --------
    say('\n(P) REPOSITORY PRIMITIVES audit/independent_clifford_q8_audit.py (tiles_at_level, panel_edges, clifford_link, q8label)')
    try:
        import sympy  # noqa
    except ImportError:
        sys.modules['sympy'] = types.ModuleType('sympy')   # only needed by the module's main(), which is not run
    spec = importlib.util.spec_from_file_location('repo_audit', os.path.join(ROOT, 'audit', 'independent_clifford_q8_audit.py'))
    RP = importlib.util.module_from_spec(spec); spec.loader.exec_module(RP)
    report['P'] = {}
    for lvl in (1, 2):
        tiles = RP.tiles_at_level(RP.FR30, lvl)
        owner, edges = RP.panel_edges(tiles)
        labels = collections.Counter()
        for (a, b, n, c, c2) in edges:
            labels[RP.q8label(RP.clifford_link(tiles[a][0], tiles[b][0], n))] += 1
        vals = {'+1': labels['+1'], '-1': labels['-1'], 'traceless': sum(v for k, v in labels.items() if k not in ('+1', '-1', 'other')), 'other': labels['other']}
        # compare the cube ownership with (R) tile by tile
        rt = ref_tiles(lvl, FR30)
        same_tiles = all(frozenset(rt[a][2]) == tiles[a][2] and (rt[a][0] == tiles[a][0]).all() for a in range(len(tiles)))
        report['P'][lvl] = {'shared_panels': len(edges), 'link_values': vals, 'labels': dict(labels), 'tiles_and_frames_identical_to_R': bool(same_tiles)}
        say(f' level {lvl}: shared panels={len(edges)} link values={vals} labels={dict(sorted(labels.items()))} tiles+frames identical to (R)={same_tiles}')

    # -------- (A) A1's module in-process --------
    say('\n(A) A1 MODULE audit/phase5a_independent_enumerator.py run in-process (no files rewritten)')
    spec = importlib.util.spec_from_file_location('a1_enum', os.path.join(ROOT, 'audit', 'phase5a_independent_enumerator.py'))
    A1 = importlib.util.module_from_spec(spec); spec.loader.exec_module(A1)
    report['A'] = {}
    for lvl in (1, 2):
        L = A1.Level(lvl); pc = L.panels_and_pauli_check(); report['A'][lvl] = pc
        say(f' level {lvl}: {pc}')
    report['A']['pauli_identity_check'] = A1.pauli_identity_check()
    say(f' A1.pauli_identity_check() (36 pairs + 64 products): {report["A"]["pauli_identity_check"]}')
    # discriminating power of A1's check: wrong embedding must make it fail
    orig = A1.q_to_mat
    def wrong_q_to_mat(a):
        base = {'1': np.eye(2, dtype=complex), 'i': 1j * A1.SIG[0], 'j': 1j * A1.SIG[1], 'k': 1j * A1.SIG[2]}[a[1]]
        return a[0] * base
    A1.q_to_mat = wrong_q_to_mat
    report['A']['pauli_identity_check_with_wrong_embedding'] = A1.pauli_identity_check()
    pc_wrong = A1.Level(1).panels_and_pauli_check()
    report['A']['level1_panel_check_with_wrong_embedding'] = pc_wrong
    A1.q_to_mat = orig
    say(f' A1.pauli_identity_check() with e_i=+i sigma_i instead: {report["A"]["pauli_identity_check_with_wrong_embedding"]} (must be False)')
    say(f' A1 level-1 panel check with e_i=+i sigma_i: pauli_agrees={pc_wrong["pauli_agrees_on_all_panels"]} (must be False); values={pc_wrong["link_values"]}')
    a1_frames = [{'perm': list(G[0]), 'signs': list(G[1]), 'T': list(T)} for G, T in zip(A1.Level(1).frames, A1.Level(1).T)]
    report['A']['level1_frames_identical_to_R'] = (a1_frames == R['level1_frames'])
    say(f' A1 level-1 frames (perm,signs,T) identical to (R) frames in the same child order: {report["A"]["level1_frames_identical_to_R"]}')

    # -------- saved outputs vs. in-process --------
    saved = json.load(open(os.path.join(OUT, 'phase5a_independent_enumerator.json'), encoding='utf-8'))
    sv = {lvl: saved['levels'][str(lvl)]['panels'] for lvl in (1, 2)}
    report['saved_json_matches_inprocess'] = all(sv[lvl] == report['A'][lvl] for lvl in (1, 2))
    say(f'\nA1 saved JSON panel entries == in-process recomputation: {report["saved_json_matches_inprocess"]}')

    # -------- verdict table --------
    claim = {1: {'shared_panels': 48, 'link_values': {'+1': 6, '-1': 24, 'traceless': 18}},
             2: {'shared_panels': 576, 'link_values': {'+1': 90, '-1': 228, 'traceless': 258}}}
    say('\nVERDICT TABLE (claimed vs. (R) vs. (P) vs. (A))')
    allok = True
    for lvl in (1, 2):
        rv = {k: R[lvl]['link_values'][k] for k in ('+1', '-1', 'traceless')}
        pv = {k: report['P'][lvl]['link_values'][k] for k in ('+1', '-1', 'traceless')}
        av = report['A'][lvl]['link_values']
        ok = (claim[lvl]['shared_panels'] == R[lvl]['shared_panels'] == report['P'][lvl]['shared_panels'] == report['A'][lvl]['shared_panels']
              and claim[lvl]['link_values'] == rv == pv == av and R[lvl]['identity_minus_i_sigma_holds_on_panels'] == R[lvl]['shared_panels']
              and R[lvl]['fills_chair_exactly'] and R[lvl]['all_links_in_Q8'])
        allok &= ok
        say(f' level {lvl}: claim panels={claim[lvl]["shared_panels"]} values={claim[lvl]["link_values"]} | R panels={R[lvl]["shared_panels"]} values={rv} | '
            f'P panels={report["P"][lvl]["shared_panels"]} values={pv} | A panels={report["A"][lvl]["shared_panels"]} values={av} | ALL AGREE: {ok}')
    report['claim_reproduced_by_all_three_paths'] = bool(allok)
    say(f'CLAIMED NUMBERS REPRODUCED BY ALL THREE CODE PATHS: {allok}')
    return report

if __name__ == '__main__':
    t0 = time.time()
    rep = main()
    rep['total_time_s'] = round(time.time() - t0, 2)
    say(f'total time {rep["total_time_s"]} s')
    os.makedirs(OUT, exist_ok=True)
    def conv(o):
        if isinstance(o, dict): return {str(k): conv(v) for k, v in o.items()}
        if isinstance(o, (list, tuple)): return [conv(v) for v in o]
        if isinstance(o, (np.integer,)): return int(o)
        if isinstance(o, (np.bool_,)): return bool(o)
        return o
    with open(os.path.join(OUT, 'phase5a_referee_links_check.json'), 'w', encoding='utf-8') as f:
        json.dump(conv(rep), f, indent=1)
    with open(os.path.join(OUT, 'phase5a_referee_links_check.txt'), 'w', encoding='utf-8') as f:
        f.write('\n'.join(LINES) + '\n')
    print('wrote audit/results/phase5a_referee_links_check.{json,txt}')
