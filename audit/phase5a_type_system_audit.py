"""
Phase 5a, Task A2 -- ADVERSARIAL AUDIT OF THE INTRINSIC TYPE SYSTEM (49 panel types / 108 plaquette types)
used by audit/phase4_type_substitution_proof.py and certificates/TypeSubstitutionCertificate.lean.

Everything below is executed, nothing is a fixture.  The phase-4 primitives (panel_type, plaquette_type_and_class,
inflate_panel, inflate_plaquette, representatives, image multisets) are obtained by exec-loading the phase-4 file
up to (excluding) its SymPy spectral section, exactly as audit/export_type_certificate.py does; the tiling itself is
cross-checked against the independent construction tiles_at_level() of audit/independent_clifford_q8_audit.py.

Sections (letters follow the task statement):
  A  validity of every representative configuration; recomputation of its own key; reconstruction of the
     configuration from the key alone (completeness of the invariant); cross-check with the Lean certificate data
  B  coverage: every inter-tile panel / plaquette of T_1..T_L has a key among the representatives; number of
     distinct keys per level; holonomy class and canonical link label are functions of the type on every instance;
     class counts agree with the recursion; inflation image multisets are well defined on ALL level-2 instances
  C  invariance of the keys under all 24 proper rotations (and the 24 improper ones), and under random rigid motions
  D  orientation / path ordering: the 8 (base cube, orientation) choices move the signed Q8 holonomy label only
     inside its conjugacy class
  E  gauge: random Q8 and random SU(2) gauge transformations on T_2 leave plaquette classes / traces unchanged
  F  negative controls: (1) face-normal reversal for one tile, (2) non-intrinsic (ambient) and coarse keys,
     (3) perturbed boundary convention (missing neighbour = present with identity link)
  G  missing-neighbour handling: edges with fewer than four present cubes are excluded; counts per level

Run from the repository root:
  python3 -u -I audit/phase5a_type_system_audit.py [--max-level 4] [--out audit/results/phase5a_type_system_audit.txt]
"""
import os, sys, io, re, json, time, argparse, contextlib, collections, itertools, random
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.dirname(HERE)
sys.path.insert(0, HERE)
from independent_clifford_q8_audit import (U3, FR30, perm_mat, tiles_at_level, panel_edges, clifford_link, q8label,
                                           sdot, SIG, fundamental_cycle_holonomies)

# ----------------------------------------------------------------------------------------------------------------
# 0. load the phase-4 derivation (type system, representatives, image multisets, recursion)
# ----------------------------------------------------------------------------------------------------------------
def load_phase4():
    path = os.path.join(HERE, 'phase4_type_substitution_proof.py')
    with open(path) as fh: src = fh.read()
    head = src.split("# ---------------- exact spectral analysis")[0]
    ns = {"__name__": "p4", "__file__": path}
    with contextlib.redirect_stdout(io.StringIO()):
        exec(compile(head, "phase4", "exec"), ns)
    return ns, src

P4, P4_SRC = load_phase4()
inflate, cubes, key, owner_map = P4['inflate'], P4['cubes'], P4['key'], P4['owner_map']
panel_type, plaquette_cubes, ptc = P4['panel_type'], P4['plaquette_cubes'], P4['plaquette_type_and_class']
inflate_panel, inflate_plaquette, inflate_config = P4['inflate_panel'], P4['inflate_plaquette'], P4['inflate_config']
loc, rel = P4['loc'], P4['rel']
E, CLASS, CLASSES = P4['E'], P4['CLASS'], P4['CLASSES']
PTYPES, QTYPES = P4['ptypes_all'], P4['qtypes_all']
PANEL_REPS, PLAQ_REPS, PLAQ_CLASS = P4['panel_reps'], P4['plaq_reps'], P4['plaq_class']
PANEL_IMG, PLAQ_IMG_FROM_PANEL, PLAQ_IMG = P4['panel_img'], P4['plaq_img_from_panel'], P4['plaq_img']
P1, PI1, REC = P4['P1'], P4['Pi1'], P4['rec']
PSET, QSET = set(PTYPES), set(QTYPES)
I2 = np.eye(2, dtype=complex)
Q8_MATS = {'+1': I2, '-1': -I2}
for k, n in enumerate('ijk'):
    Q8_MATS[f'+{n}'] = 1j*SIG[k]; Q8_MATS[f'-{n}'] = -1j*SIG[k]
INV = {'+1': '+1', '-1': '-1', '+i': '-i', '-i': '+i', '+j': '-j', '-j': '+j', '+k': '-k', '-k': '+k'}

def ival(x):
    """Recursively convert numpy integers inside nested tuples to Python ints (for printing / JSON)."""
    if isinstance(x, (tuple, list)): return tuple(ival(y) for y in x)
    if isinstance(x, np.generic): return x.item()
    return x

# ----------------------------------------------------------------------------------------------------------------
# 1. the hyperoctahedral group and rigid motions of the cube lattice
# ----------------------------------------------------------------------------------------------------------------
def signed_perms(det=None):
    out = []
    for p in itertools.permutations(range(3)):
        for signs in itertools.product((1, -1), repeat=3):
            M = np.zeros((3, 3), int)
            for r in range(3): M[r, p[r]] = signs[r]
            d = int(round(np.linalg.det(M)))
            if det is None or d == det: out.append(M)
    return out
SO3Z = signed_perms(1); REFL = signed_perms(-1)
assert len(SO3Z) == 24 and len(REFL) == 24

def is_so3z(G):
    G = np.asarray(G)
    return G.dtype.kind in 'iu' and (G.T @ G == np.eye(3, dtype=int)).all() and int(round(np.linalg.det(G))) == 1

def move_pose(R, s, p): return (R @ p[0], R @ p[1] + np.asarray(s, int))
def move_cube(R, s, c):
    x = R @ (2*np.asarray(c, int) + 1) + 2*np.asarray(s, int)     # doubled centre transforms affinely
    return tuple(int(v) for v in (x - 1)//2)
def axis_of(v): return int(np.argmax(np.abs(v)))

def move_panel_rep(R, s, rep):
    poses, c, ax = rep
    nposes = [move_pose(R, s, p) for p in poses]
    c1, c2 = move_cube(R, s, c), move_cube(R, s, np.asarray(c, int) + E[ax])
    return nposes, tuple(min(a, b) for a, b in zip(c1, c2)), axis_of(R @ E[ax])

def move_plaq_rep(R, s, rep):
    poses, c, i, j = rep
    nposes = [move_pose(R, s, p) for p in poses]
    cs = [move_cube(R, s, x) for x in plaquette_cubes(c, i, j)]
    base = tuple(min(x[d] for x in cs) for d in range(3))
    ni, nj = sorted((axis_of(R @ E[i]), axis_of(R @ E[j])))
    return nposes, base, ni, nj

def tiles_disjoint(poses):
    seen, distinct = set(), {key(*p): p for p in poses}
    for p in distinct.values():
        cs = set(cubes(*p))
        if cs & seen: return False
        seen |= cs
    return True

# ----------------------------------------------------------------------------------------------------------------
# 2. tiling construction and enumeration helpers
# ----------------------------------------------------------------------------------------------------------------
def build_level(m):
    poses = [(np.eye(3, dtype=int), np.zeros(3, dtype=int))]
    for _ in range(m): poses = [q for p in poses for q in inflate(*p)]
    return poses, owner_map(poses)

def same_tiling_as_independent(m):
    poses, _ = build_level(m); tl = tiles_at_level(FR30, m)
    s1 = {(key(G, T), frozenset(cubes(G, T))) for G, T in poses}
    s2 = {(key(G, T), cs) for G, T, cs in tl}
    return s1 == s2

def iter_panels(om):
    """All inter-tile unit panels: (lower cube, axis, intrinsic type)."""
    for c, pose in om.items():
        for ax in range(3):
            c2 = tuple(np.asarray(c, int) + E[ax])
            if c2 in om and key(*om[c2]) != key(*pose):
                yield c, ax, panel_type(om, c, ax)

def iter_plaquettes(om, include_intra=False):
    """All lattice edges with four present cubes: (base cube, i, j, type or None, class or None)."""
    for c in om:
        for (i, j) in ((0, 1), (0, 2), (1, 2)):
            cs = plaquette_cubes(c, i, j)
            if all(x in om for x in cs):
                t, cl = ptc(om, c, i, j)
                if t is not None or include_intra: yield c, i, j, t, cl

def panel_canonical_link_label(om, c, ax):
    """Signed Q8 label of the link read in the canonical (minimal-encoding) ordering of the panel."""
    c2 = tuple(np.asarray(c, int) + E[ax]); p, p2 = om[c], om[c2]
    e1 = (loc(*p, c), tuple(p[0].T @ E[ax]), rel(*p, *p2))
    e2 = (loc(*p2, c2), tuple(p2[0].T @ (-E[ax])), rel(*p2, *p))
    if e1 <= e2: return q8label(clifford_link(p[0], p2[0], E[ax]))
    return q8label(clifford_link(p2[0], p[0], -E[ax]))

def link_between(om, x, y, link_fn=None):
    px, py = om[x], om[y]
    if key(*px) == key(*py): return I2
    n = np.asarray(y, int) - np.asarray(x, int)
    return (link_fn or clifford_link)(px[0], py[0], n)

def holonomy(om, seq, link_fn=None):
    W = I2.copy()
    for q in range(len(seq)): W = W @ link_between(om, seq[q], seq[(q+1) % len(seq)], link_fn)
    return W

def holonomy_labels_all_orderings(om, cs, link_fn=None):
    """The 8 signed labels (start cube x orientation) of the plaquette around the edge shared by cs."""
    out = {}
    for start in range(4):
        for rev, order in ((0, cs), (1, cs[::-1])):
            seq = order[start:] + order[:start]
            out[(start, rev)] = q8label(holonomy(om, seq, link_fn))
    return out

# ----------------------------------------------------------------------------------------------------------------
# A. representatives
# ----------------------------------------------------------------------------------------------------------------
def panel_config_from_key(t):
    """Rebuild a configuration from the key alone (reference tile at the identity pose)."""
    locv, nloc, (Grel, trel) = t
    ref = (np.eye(3, dtype=int), np.zeros(3, dtype=int)); other = (np.array(Grel, int), np.array(trel, int))
    c = tuple(int(v) for v in (np.array(locv, int) - 1)//2); ax = axis_of(np.array(nloc, int))
    low = c if nloc[ax] > 0 else tuple(int(v) for v in np.asarray(c, int) - E[ax])
    return [ref, other], low, ax

def plaq_config_from_key(t):
    poses = [(np.array(G, int), np.array(tr, int)) for (_, (G, tr)) in t]
    cs = [tuple(int(v) for v in (np.array(l, int) - 1)//2) for (l, _) in t]
    base = tuple(min(x[d] for x in cs) for d in range(3))
    axes = sorted({d for x in cs for d in range(3) if x[d] != base[d]})
    return poses, cs, base, axes

def panel_config_signature(poses, c, ax):
    c2 = tuple(int(v) for v in np.asarray(c, int) + E[ax])
    return (frozenset(ival(key(*p)) for p in poses), frozenset({ival(tuple(c)), c2}))

def check_panel_representatives():
    res = {'n': len(PTYPES), 'invalid_config': [], 'key_mismatch': [], 'reconstruction_fail': [], 'not_gamma_equivalent': []}
    for n, t in enumerate(PTYPES):
        poses, c, ax = PANEL_REPS[t]; p, p2 = poses; c2 = tuple(np.asarray(c, int) + E[ax])
        valid = (len(poses) == 2 and all(is_so3z(q[0]) for q in poses) and key(*p) != key(*p2) and tiles_disjoint(poses)
                 and tuple(c) in set(cubes(*p)) and c2 in set(cubes(*p2)))
        if not valid: res['invalid_config'].append(n)
        if panel_type(owner_map(poses), tuple(c), ax) != t: res['key_mismatch'].append(n)
        # completeness: the key alone rebuilds a valid configuration with the same key ...
        rposes, rlow, rax = panel_config_from_key(t)
        rc2 = tuple(np.asarray(rlow, int) + E[rax])
        rvalid = (tiles_disjoint(rposes) and key(*rposes[0]) != key(*rposes[1])
                  and (rlow in set(cubes(*rposes[0])) and rc2 in set(cubes(*rposes[1]))
                       or rlow in set(cubes(*rposes[1])) and rc2 in set(cubes(*rposes[0]))))
        if not (rvalid and panel_type(owner_map(rposes), rlow, rax) == t): res['reconstruction_fail'].append(n)
        # ... and that configuration is carried onto the representative by the rigid motion (G_ref, T_ref)
        e1 = (loc(*p, c), tuple(p[0].T @ E[ax]), rel(*p, *p2))
        ref = p if e1 == t else p2
        moved = move_panel_rep(ref[0], ref[1], (rposes, rlow, rax))
        if panel_config_signature(*moved) != panel_config_signature(poses, c, ax): res['not_gamma_equivalent'].append(n)
    res['ok'] = not any(res[k] for k in ('invalid_config', 'key_mismatch', 'reconstruction_fail', 'not_gamma_equivalent'))
    return res

def check_plaquette_representatives():
    res = {'n': len(QTYPES), 'invalid_config': [], 'key_mismatch': [], 'class_mismatch': [], 'reconstruction_fail': [],
           'not_gamma_equivalent': [], 'distinct_tiles_hist': collections.Counter()}
    for n, t in enumerate(QTYPES):
        poses, c, i, j = PLAQ_REPS[t]; cs = plaquette_cubes(c, i, j)
        ndist = len({key(*q) for q in poses}); res['distinct_tiles_hist'][ndist] += 1
        valid = (len(poses) == 4 and i < j and all(is_so3z(q[0]) for q in poses) and tiles_disjoint(poses) and ndist >= 2
                 and all(tuple(cs[q]) in set(cubes(*poses[q])) for q in range(4)))
        if not valid: res['invalid_config'].append(n)
        tt, cl = ptc(owner_map(poses), tuple(c), i, j)
        if tt != t: res['key_mismatch'].append(n)
        if cl != PLAQ_CLASS[t]: res['class_mismatch'].append(n)
        rposes, rcs, rbase, raxes = plaq_config_from_key(t)
        rvalid = (len(raxes) == 2 and set(rcs) == set(plaquette_cubes(rbase, *raxes)) and tiles_disjoint(rposes)
                  and all(rcs[q] in set(cubes(*rposes[q])) for q in range(4)))
        rtt, rcl = ptc(owner_map(rposes), rbase, *raxes) if rvalid else (None, None)
        if not (rvalid and rtt == t and rcl == PLAQ_CLASS[t]): res['reconstruction_fail'].append(n)
        # Gamma-equivalence: the reference tile of the canonical encoding is the owner of the first cube of the
        # canonical sequence; its pose (G,T) carries the rebuilt configuration onto the representative
        om = owner_map(poses); found = False
        for start in range(4):
            for order in (cs, cs[::-1]):
                seq = order[start:] + order[:start]; ref = om[seq[0]]
                if tuple((loc(*ref, x), rel(*ref, *om[x])) for x in seq) == t:
                    moved = move_plaq_rep(ref[0], ref[1], (rposes, rbase, raxes[0], raxes[1]))
                    sig_m = ({ival(key(*q)) for q in moved[0]}, set(plaquette_cubes(moved[1], moved[2], moved[3])))
                    sig_r = ({ival(key(*q)) for q in poses}, set(ival(x) for x in cs))
                    found = found or sig_m == sig_r
        if not found: res['not_gamma_equivalent'].append(n)
    res['distinct_tiles_hist'] = dict(sorted(res['distinct_tiles_hist'].items()))
    res['ok'] = not any(res[k] for k in ('invalid_config', 'key_mismatch', 'class_mismatch', 'reconstruction_fail', 'not_gamma_equivalent'))
    return res

def lean_certificate_reps_match():
    """Parse panelReps / plaqReps from the Lean certificate and compare with the Python representatives (same order)."""
    path = os.path.join(ROOT, 'certificates', 'TypeSubstitutionCertificate.lean')
    if not os.path.exists(path): return {'present': False}
    with open(path) as fh: txt = fh.read()
    def block(name):
        seg = txt.split(f"def {name}", 1)[1].split("\n]", 1)[0]
        return [[int(v) for v in re.findall(r'-?\d+', ln)] for ln in seg.split("\n") if ln.strip().startswith("([")]
    lp, lq = block("panelReps"), block("plaqReps")
    def flat_pose(p): return [int(v) for v in np.asarray(p[0], int).ravel()] + [int(v) for v in np.asarray(p[1], int)]
    pp = [sum((flat_pose(p) for p in PANEL_REPS[t][0]), []) + [int(v) for v in PANEL_REPS[t][1]] + [int(PANEL_REPS[t][2])] for t in PTYPES]
    pq = [sum((flat_pose(p) for p in PLAQ_REPS[t][0]), []) + [int(v) for v in PLAQ_REPS[t][1]] + [int(PLAQ_REPS[t][2]), int(PLAQ_REPS[t][3])] for t in QTYPES]
    return {'present': True, 'lean_panel_reps': len(lp), 'lean_plaq_reps': len(lq), 'panel_match': lp == pp, 'plaq_match': lq == pq,
            'ints_per_panel_line': sorted({len(l) for l in lp}), 'ints_per_plaq_line': sorted({len(l) for l in lq})}

def representatives_pairwise_distinct():
    return len(PSET) == len(PTYPES) and len(QSET) == len(QTYPES)

# ----------------------------------------------------------------------------------------------------------------
# B. coverage
# ----------------------------------------------------------------------------------------------------------------
def coverage_level(m, check_images=False):
    t0 = time.time(); poses, om = build_level(m)
    out = {'level': m, 'tiles': len(poses), 'cubes': len(om)}
    pk = collections.Counter(); unknown_p = 0; link_of_type = {}; link_conflicts = 0; panels = []
    for c, ax, t in iter_panels(om):
        pk[t] += 1; panels.append((c, ax, t))
        if t not in PSET: unknown_p += 1
        lab = panel_canonical_link_label(om, c, ax)
        if link_of_type.setdefault(t, lab) != lab: link_conflicts += 1
    qk = collections.Counter(); unknown_q = 0; class_conflicts = 0; cls = collections.Counter(); plaqs = []
    for c, i, j, t, cl in iter_plaquettes(om):
        qk[t] += 1; cls[cl] += 1; plaqs.append((c, i, j, t, cl))
        if t not in QSET: unknown_q += 1
        elif PLAQ_CLASS[t] != cl: class_conflicts += 1
    out.update(panels=sum(pk.values()), panel_types=len(pk), panel_unknown=unknown_p, link_label_conflicts=link_conflicts,
               plaquettes=sum(qk.values()), plaq_types=len(qk), plaq_unknown=unknown_q, class_conflicts=class_conflicts,
               class_counts={c: cls[c] for c in CLASSES}, recursion_counts={c: REC[m][c] for c in CLASSES} if m in REC else None,
               panel_type_counts_match_recursion=None, seconds=round(time.time() - t0, 1))
    out['class_counts_match_recursion'] = (out['class_counts'] == out['recursion_counts']) if out['recursion_counts'] else None
    # type-resolved comparison with the recursion (level 1: the seed; level m: iterate the phase-4 step)
    P, Pi = P1, PI1
    for mm in range(1, m): P, Pi = P4['step'](P, Pi, mm)
    out['panel_type_counts_match_recursion'] = (pk == P); out['plaq_type_counts_match_recursion'] = (qk == Pi)
    if check_images:
        bad_p = bad_q = 0
        for c, ax, t in panels:
            c2 = tuple(np.asarray(c, int) + E[ax]); ptypes, pl = inflate_panel(([om[c], om[c2]], c, ax))
            if (collections.Counter(ptypes) != PANEL_IMG[t] or collections.Counter(tt for tt, _ in pl) != PLAQ_IMG_FROM_PANEL[t]
                    or any(PLAQ_CLASS[tt] != cl for tt, cl in pl)): bad_p += 1
        for c, i, j, t, cl in plaqs:
            res = inflate_plaquette(([om[x] for x in plaquette_cubes(c, i, j)], c, i, j))
            if collections.Counter(tt for tt, _ in res) != PLAQ_IMG[t] or any(PLAQ_CLASS[tt] != cl2 for tt, cl2 in res): bad_q += 1
        out.update(image_checked_panels=len(panels), image_bad_panels=bad_p, image_checked_plaqs=len(plaqs), image_bad_plaqs=bad_q)
    out['_panel_keys'] = set(pk); out['_plaq_keys'] = set(qk)
    return out

# ----------------------------------------------------------------------------------------------------------------
# C. invariance
# ----------------------------------------------------------------------------------------------------------------
def ambient_panel_key(poses, c, ax):
    return (ival(tuple(c)), ax, tuple(sorted(ival(key(*p)) for p in poses)))

def invariance_test(n_random=50, seed=20251021, tmax=(-30, 30)):
    rng = random.Random(seed)
    res = collections.Counter(); res['panel_reps'] = len(PTYPES); res['plaq_reps'] = len(QTYPES)
    first_fail = []
    for t in PTYPES:
        rep = PANEL_REPS[t]
        motions = [(R, np.zeros(3, int)) for R in SO3Z] + [(R, np.zeros(3, int)) for R in REFL]
        motions += [(rng.choice(SO3Z), np.array([rng.randint(*tmax) for _ in range(3)])) for _ in range(n_random)]
        for n, (R, s) in enumerate(motions):
            nposes, low, nax = move_panel_rep(R, s, rep)
            tt = panel_type(owner_map(nposes), low, nax)
            tag = 'SO3' if n < 24 else ('REFL' if n < 48 else 'RAND')
            res[f'panel_{tag}_checks'] += 1
            if tt != t:
                res[f'panel_{tag}_fail'] += 1
                if len(first_fail) < 5: first_fail.append(('panel', PTYPES.index(t), tag, R.tolist(), s.tolist()))
            if ambient_panel_key(nposes, low, nax) != ambient_panel_key(rep[0], rep[1], rep[2]): res[f'ambient_panel_{tag}_changed'] += 1
    for t in QTYPES:
        rep = PLAQ_REPS[t]
        motions = [(R, np.zeros(3, int)) for R in SO3Z] + [(R, np.zeros(3, int)) for R in REFL]
        motions += [(rng.choice(SO3Z), np.array([rng.randint(*tmax) for _ in range(3)])) for _ in range(n_random)]
        for n, (R, s) in enumerate(motions):
            nposes, base, ni, nj = move_plaq_rep(R, s, rep)
            tt, cl = ptc(owner_map(nposes), base, ni, nj)
            tag = 'SO3' if n < 24 else ('REFL' if n < 48 else 'RAND')
            res[f'plaq_{tag}_checks'] += 1
            if tt != t:
                res[f'plaq_{tag}_fail'] += 1
                if len(first_fail) < 5: first_fail.append(('plaq', QTYPES.index(t), tag, R.tolist(), s.tolist()))
            if cl != PLAQ_CLASS[t]: res[f'plaq_{tag}_class_fail'] += 1
    for kind in ('panel', 'plaq'):
        for tag in ('SO3', 'REFL', 'RAND'):
            res[f'{kind}_{tag}_fail'] += 0
            if kind == 'plaq': res[f'plaq_{tag}_class_fail'] += 0
    out = dict(res); out['first_failures'] = first_fail
    out['ok_proper'] = all(res[k] == 0 for k in ('panel_SO3_fail', 'plaq_SO3_fail', 'panel_RAND_fail', 'plaq_RAND_fail',
                                                 'plaq_SO3_class_fail', 'plaq_RAND_class_fail'))
    out['ok_improper_also_invariant'] = res['panel_REFL_fail'] == 0 and res['plaq_REFL_fail'] == 0
    return out

# ----------------------------------------------------------------------------------------------------------------
# D. orientation / path ordering
# ----------------------------------------------------------------------------------------------------------------
def orientation_test_on(om, items):
    """items: iterable of (base cube, i, j).  Returns statistics of the 8 signed labels per plaquette."""
    res = collections.Counter(); examples = {}
    for c, i, j in items:
        cs = plaquette_cubes(c, i, j); labs = holonomy_labels_all_orderings(om, cs)
        classes = {CLASS[l] for l in labs.values()}
        res['plaquettes'] += 1
        if len(classes) != 1: res['class_changed'] += 1
        if 'other' in labs.values(): res['non_q8'] += 1
        cl = next(iter(classes))
        signed = set(labs.values())
        if len(signed) == 1: res[f'constant_label_{cl}'] += 1
        else: res[f'sign_varies_{cl}'] += 1
        # reversal = inverse: label(order cs, start k) and label(order reversed, start 3-k) are mutually inverse
        if all(INV[labs[(k, 0)]] == labs[(3 - k, 1)] for k in range(4)): res['reversal_is_inverse'] += 1
        else: res['reversal_not_inverse'] += 1
        # base change = conjugation by the link: W_{k+1} = C^{-1} W_k C  (checked on matrices)
        seqs = [cs[k:] + cs[:k] for k in range(4)]
        Ws = [holonomy(om, s) for s in seqs]
        conj_ok = True
        for k in range(4):
            C = link_between(om, cs[k], cs[(k + 1) % 4])
            conj_ok &= np.allclose(Ws[(k + 1) % 4], C.conj().T @ Ws[k] @ C)
        res['base_change_is_conjugation' if conj_ok else 'base_change_not_conjugation'] += 1
        examples.setdefault(cl, (ival(tuple(c)), i, j, {str(k): v for k, v in labs.items()}))
    return dict(res), examples

def orientation_test_reps():
    res = collections.Counter()
    for t in QTYPES:
        poses, c, i, j = PLAQ_REPS[t]; om = owner_map(poses)
        r, _ = orientation_test_on(om, [(c, i, j)])
        for k, v in r.items(): res[k] += v
    return dict(res)

def orientation_test_level(m):
    poses, om = build_level(m)
    items_inter = [(c, i, j) for c, i, j, t, cl in iter_plaquettes(om)]
    items_all = [(c, i, j) for c, i, j, t, cl in iter_plaquettes(om, include_intra=True)]
    r_inter, ex = orientation_test_on(om, items_inter); r_all, _ = orientation_test_on(om, items_all)
    return {'inter_tile': r_inter, 'all_four_present': r_all, 'examples': ex}

# ----------------------------------------------------------------------------------------------------------------
# E. gauge
# ----------------------------------------------------------------------------------------------------------------
def random_su2(rng):
    q = rng.normal(size=4); q /= np.linalg.norm(q)
    return q[0]*I2 + 1j*(q[1]*SIG[0] + q[2]*SIG[1] + q[3]*SIG[2])

def gauge_test(m=2, seed=20251021, n_rounds=3):
    rng = np.random.default_rng(seed); pyrng = random.Random(seed)
    poses, om = build_level(m)
    tid = {key(*p): n for n, p in enumerate(poses)}
    links = {}   # directed cube pair -> matrix, inter-tile only
    for c, ax, t in iter_panels(om):
        c2 = tuple(np.asarray(c, int) + E[ax]); C = clifford_link(om[c][0], om[c2][0], E[ax])
        links[(c, c2)] = C; links[(c2, c)] = C.conj().T
    plaqs = [plaquette_cubes(c, i, j) for c, i, j, t, cl in iter_plaquettes(om, include_intra=True)]
    def W_of(cs, L):
        W = I2.copy()
        for q in range(4):
            x, y = cs[q], cs[(q + 1) % 4]
            W = W @ (L[(x, y)] if (x, y) in L else I2)
        return W
    base_W = [W_of(cs, links) for cs in plaqs]
    base_lab = [q8label(W) for W in base_W]
    tiles = tiles_at_level(FR30, m); owner, edges = panel_edges(tiles)
    tlinks = [clifford_link(tiles[a][0], tiles[b][0], nf) for a, b, nf, _, _ in edges]
    base_cycles = collections.Counter(CLASS[q8label(h)] for h in fundamental_cycle_holonomies(len(tiles), edges, tlinks))
    out = {'level': m, 'tiles': len(poses), 'inter_tile_links': len(links)//2, 'plaquettes_checked': len(plaqs),
           'fundamental_cycles': sum(base_cycles.values()), 'rounds': []}
    for rnd in range(n_rounds):
        # --- Q8 gauge ---
        Gq = {n: Q8_MATS[pyrng.choice(list(Q8_MATS))] for n in range(len(poses))}
        Lq = {(x, y): Gq[tid[key(*om[x])]] @ C @ Gq[tid[key(*om[y])]].conj().T for (x, y), C in links.items()}
        changed_q = sum(1 for k in links if (k[0] < k[1]) and not np.allclose(Lq[k], links[k]))
        labs_q = [q8label(W_of(cs, Lq)) for cs in plaqs]
        class_changed_q = sum(1 for a, b in zip(base_lab, labs_q) if CLASS[a] != CLASS[b])
        signed_changed_q = sum(1 for a, b in zip(base_lab, labs_q) if a != b)
        non_q8 = sum(1 for l in labs_q if l == 'other')
        tl_q = [Gq[a] @ C @ Gq[b].conj().T for (a, b, nf, _, _), C in zip(edges, tlinks)]
        cyc_q = collections.Counter(CLASS[q8label(h)] for h in fundamental_cycle_holonomies(len(tiles), edges, tl_q))
        # --- SU(2) gauge ---
        Gs = {n: random_su2(rng) for n in range(len(poses))}
        Ls = {(x, y): Gs[tid[key(*om[x])]] @ C @ Gs[tid[key(*om[y])]].conj().T for (x, y), C in links.items()}
        changed_s = sum(1 for k in links if (k[0] < k[1]) and not np.allclose(Ls[k], links[k]))
        in_q8_s = sum(1 for k in links if (k[0] < k[1]) and q8label(Ls[k]) != 'other')
        tr_dev = max(abs(np.trace(W_of(cs, Ls)) - np.trace(W0)) for cs, W0 in zip(plaqs, base_W))
        tl_s = [Gs[a] @ C @ Gs[b].conj().T for (a, b, nf, _, _), C in zip(edges, tlinks)]
        cyc_tr_dev = max(abs(np.trace(h1) - np.trace(h0)) for h0, h1 in
                         zip(fundamental_cycle_holonomies(len(tiles), edges, tlinks), fundamental_cycle_holonomies(len(tiles), edges, tl_s)))
        out['rounds'].append({'q8_links_changed': changed_q, 'q8_signed_labels_changed': signed_changed_q, 'q8_classes_changed': class_changed_q,
                              'q8_non_q8_holonomies': non_q8, 'q8_cycle_classes_unchanged': cyc_q == base_cycles,
                              'su2_links_changed': changed_s, 'su2_links_still_in_q8': in_q8_s, 'su2_max_trace_deviation': float(tr_dev),
                              'su2_cycle_max_trace_deviation': float(cyc_tr_dev)})
    out['ok'] = all(r['q8_classes_changed'] == 0 and r['q8_non_q8_holonomies'] == 0 and r['q8_cycle_classes_unchanged']
                    and r['su2_max_trace_deviation'] < 1e-9 and r['su2_cycle_max_trace_deviation'] < 1e-9 for r in out['rounds'])
    out['links_change_under_gauge'] = all(r['q8_links_changed'] > 0 and r['su2_links_changed'] > 0 for r in out['rounds'])
    return out

# ----------------------------------------------------------------------------------------------------------------
# F. negative controls
# ----------------------------------------------------------------------------------------------------------------
def negative_normal_reversal(m=1, star_index=3):
    """Perturbations of the link construction applied to ONE tile (tile number star_index of T_m)."""
    poses, om = build_level(m); star = key(*poses[star_index])
    P3 = perm_mat((1, 2, 0))        # 3-cycle (even permutation; the chair point-set is invariant under it)
    def make(kind):
        def link(px, py, n):
            ua, ub = px[0].T @ n, py[0].T @ n; sa = sb = 1
            if kind == 'reverse_normal_in_star_factor':
                if key(*px) == star: ua = -ua
                if key(*py) == star: ub = -ub
            elif kind == 'reverse_normal_both_factors_if_star':
                if star in (key(*px), key(*py)): ua, ub = -ua, -ub
            elif kind == 'reverse_normal_globally':
                ua, ub = -ua, -ub
            elif kind == 'forget_frame_of_star':
                if key(*px) == star: ua = n
                if key(*py) == star: ub = n
            elif kind == 'permute_local_normal_of_star':
                if key(*px) == star: ua = P3 @ ua
                if key(*py) == star: ub = P3 @ ub
            return sdot(ua) @ sdot(ub)
        return link
    def run(link):
        labs, links = {}, {}
        for c, i, j, t, cl in iter_plaquettes(om):
            cs = plaquette_cubes(c, i, j); W = I2.copy()
            for q in range(4):
                x, y = cs[q], cs[(q + 1) % 4]
                if key(*om[x]) != key(*om[y]): W = W @ link(om[x], om[y], np.asarray(y, int) - np.asarray(x, int))
            labs[(c, i, j)] = q8label(W)
        for c, ax, t in iter_panels(om):
            c2 = tuple(np.asarray(c, int) + E[ax]); links[(c, ax)] = q8label(link(om[c], om[c2], E[ax]))
        return labs, links
    base_labs, base_links = run(make('baseline'))
    base_counts = collections.Counter(CLASS[l] for l in base_labs.values())
    out = {'level': m, 'star_tile': star_index, 'links_incident_to_star': sum(1 for (c, ax) in base_links if star in (key(*om[c]), key(*om[tuple(np.asarray(c, int) + E[ax])]))),
           'baseline_class_counts': {c: base_counts[c] for c in CLASSES}, 'variants': {}}
    for kind in ('reverse_normal_in_star_factor', 'reverse_normal_both_factors_if_star', 'reverse_normal_globally',
                 'forget_frame_of_star', 'permute_local_normal_of_star'):
        labs, links = run(make(kind)); cnt = collections.Counter(CLASS[l] for l in labs.values())
        touching = [k for k in labs if star in {key(*om[x]) for x in plaquette_cubes(*k)}]
        out['variants'][kind] = {
            'links_changed': sum(1 for k in links if links[k] != base_links[k]),
            'plaquettes_touching_star': len(touching),
            'plaquette_classes_changed': sum(1 for k in labs if CLASS[labs[k]] != CLASS[base_labs[k]]),
            'plaquette_signed_labels_changed': sum(1 for k in labs if labs[k] != base_labs[k]),
            'non_q8_holonomies': sum(1 for l in labs.values() if l == 'other'),
            'class_counts': {c: cnt[c] for c in CLASSES}}
    return out

def negative_ambient_key(m=2):
    """A non-intrinsic key (ambient cube, axis, ambient poses) is not Gamma-invariant and separates instances of
    one intrinsic type; a key coarser than the intrinsic one (relative pose only) is Gamma-invariant but does NOT
    determine the inflation image multiset."""
    poses, om = build_level(m)
    by_intr = collections.defaultdict(list)
    for c, ax, t in iter_panels(om):
        c2 = tuple(np.asarray(c, int) + E[ax]); by_intr[t].append(ambient_panel_key([om[c], om[c2]], c, ax))
    multi = {t: v for t, v in by_intr.items() if len(v) >= 2}
    example = None
    for t, v in multi.items():
        if v[0] != v[1]: example = (PTYPES.index(t), v[0], v[1]); break
    n_intr_types_with_several_ambient_keys = sum(1 for v in multi.values() if len(set(v)) >= 2)
    # coarse keys (invariant but not complete): panel -> relative pose only; plaquette -> multiset of relative frames
    coarse_img = collections.defaultdict(set); coarse_intr = collections.defaultdict(set)
    for c, ax, t in iter_panels(om):
        c2 = tuple(np.asarray(c, int) + E[ax]); p, p2 = om[c], om[c2]
        ck = min(rel(*p, *p2), rel(*p2, *p))
        ptypes, pl = inflate_panel(([p, p2], c, ax))
        img = (tuple(sorted(collections.Counter(ptypes).items(), key=lambda kv: PTYPES.index(kv[0]))),
               tuple(sorted(collections.Counter(tt for tt, _ in pl).items(), key=lambda kv: QTYPES.index(kv[0]))))
        coarse_img[ck].add(img); coarse_intr[ck].add(t)
    coarse_frame_img = collections.defaultdict(set); coarse_frame_intr = collections.defaultdict(set)
    for c, i, j, t, cl in iter_plaquettes(om):
        cs = plaquette_cubes(c, i, j); ps = [om[x] for x in cs]
        frames = tuple(sorted(collections.Counter(tuple(map(tuple, ps[0][0].T @ q[0])) for q in ps).items()))
        res = inflate_plaquette((ps, c, i, j))
        img = tuple(sorted(collections.Counter(tt for tt, _ in res).items(), key=lambda kv: QTYPES.index(kv[0])))
        coarse_frame_img[frames].add((img, cl)); coarse_frame_intr[frames].add(t)
    return {'level': m, 'intrinsic_panel_types_with_several_instances': len(multi),
            'intrinsic_types_whose_instances_have_different_ambient_keys': n_intr_types_with_several_ambient_keys,
            'example_equal_intrinsic_different_ambient': ival(example),
            'coarse_panel_keys': len(coarse_img), 'coarse_panel_keys_merging_several_intrinsic_types': sum(1 for v in coarse_intr.values() if len(v) > 1),
            'coarse_panel_keys_with_conflicting_images': sum(1 for v in coarse_img.values() if len(v) > 1),
            'coarse_plaq_keys': len(coarse_frame_img), 'coarse_plaq_keys_merging_several_intrinsic_types': sum(1 for v in coarse_frame_intr.values() if len(v) > 1),
            'coarse_plaq_keys_with_conflicting_images_or_classes': sum(1 for v in coarse_frame_img.values() if len(v) > 1),
            'coarse_plaq_keys_with_conflicting_classes': sum(1 for v in coarse_frame_img.values() if len({cl for _, cl in v}) > 1)}

def all_edges(om):
    """Every lattice edge adjacent to at least one present cube: (base, i, j) -> list of present/missing flags."""
    seen = {}
    for c in om:
        for (i, j) in ((0, 1), (0, 2), (1, 2)):
            for di in (0, 1):
                for dj in (0, 1):
                    base = tuple(int(v) for v in np.asarray(c, int) - di*E[i] - dj*E[j])
                    if (base, i, j) not in seen:
                        cs = plaquette_cubes(base, i, j)
                        seen[(base, i, j)] = [x in om for x in cs]
    return seen

def negative_boundary_convention(m=1):
    """Treat a missing neighbour as present with identity link and count 'plaquettes' around every edge with at
    least two distinct tiles among its present cubes (the correct convention requires all four cubes present)."""
    poses, om = build_level(m); edges = all_edges(om)
    strict = collections.Counter(); loose = collections.Counter(); n_strict = n_loose = 0
    for (base, i, j), present in edges.items():
        cs = plaquette_cubes(base, i, j)
        tiles = {key(*om[x]) for x, p in zip(cs, present) if p}
        if len(tiles) < 2: continue
        W = I2.copy()
        for q in range(4):
            x, y = cs[q], cs[(q + 1) % 4]
            if present[q] and present[(q + 1) % 4] and key(*om[x]) != key(*om[y]):
                W = W @ clifford_link(om[x][0], om[y][0], np.asarray(y, int) - np.asarray(x, int))
        cl = CLASS.get(q8label(W), 'other'); loose[cl] += 1; n_loose += 1
        if all(present): strict[cl] += 1; n_strict += 1
    return {'level': m, 'strict_total': n_strict, 'strict_counts': {c: strict[c] for c in CLASSES},
            'strict_1_m1_tr0': (strict['1'], strict['-1'], strict['i'] + strict['j'] + strict['k']),
            'loose_total': n_loose, 'loose_counts': {c: loose[c] for c in CLASSES}, 'loose_non_q8': loose['other'],
            'loose_1_m1_tr0': (loose['1'], loose['-1'], loose['i'] + loose['j'] + loose['k']),
            'extra_edges_counted_by_loose_convention': n_loose - n_strict}

# ----------------------------------------------------------------------------------------------------------------
# G. missing-neighbour handling
# ----------------------------------------------------------------------------------------------------------------
def missing_neighbour_census(m):
    poses, om = build_level(m); edges = all_edges(om)
    hist = collections.Counter(); excluded_multi = excluded_any = 0; four_inter = four_intra = 0
    for (base, i, j), present in edges.items():
        cs = plaquette_cubes(base, i, j); n = sum(present)
        ntiles = len({key(*om[x]) for x, p in zip(cs, present) if p})
        hist[(n, min(ntiles, 2))] += 1
        if n < 4:
            excluded_any += 1
            if ntiles >= 2: excluded_multi += 1
        else:
            if ntiles >= 2: four_inter += 1
            else: four_intra += 1
    n_phase4 = sum(1 for _ in iter_plaquettes(om))
    return {'level': m, 'cubes': len(om), 'edges_adjacent_to_tiling': len(edges),
            'hist_(present_cubes, min(tiles,2))': {f'{k[0]} present, {"inter" if k[1] == 2 else "single"}-tile': v for k, v in sorted(hist.items())},
            'excluded_lt4_present': excluded_any, 'excluded_lt4_present_touching_2plus_tiles': excluded_multi,
            'four_present_inter_tile': four_inter, 'four_present_intra_tile': four_intra,
            'phase4_enumeration_count': n_phase4, 'phase4_equals_four_present_inter_tile': n_phase4 == four_inter}

def source_conventions():
    with open(os.path.join(ROOT, 'certificates', 'TypeSubstitutionCertificate.lean')) as fh: lean = fh.read()
    return {'phase4_seed_requires_all_four_present': 'if all(x in om1 for x in cs):' in P4_SRC,
            'phase4_rep_search_requires_all_four_present': 'all(x in om for x in cs) and plaquette_type_and_class' in P4_SRC,
            'phase4_returns_None_for_single_tile': 'if len(keys) == 1: return None, None' in P4_SRC,
            'lean_isInterTilePlaquette_requires_allPresent': 'allPresent om cs && !(allSameTile om cs)' in lean}

# ----------------------------------------------------------------------------------------------------------------
# driver
# ----------------------------------------------------------------------------------------------------------------
class Tee:
    def __init__(self, path): self.f = open(path, 'w'); self.o = sys.stdout
    def write(self, s): self.f.write(s); self.o.write(s)
    def flush(self): self.f.flush(); self.o.flush()

def jsonable(x):
    if isinstance(x, dict): return {str(k): jsonable(v) for k, v in x.items() if not str(k).startswith('_')}
    if isinstance(x, (list, tuple, set, frozenset)): return [jsonable(v) for v in x]
    if isinstance(x, np.generic): return x.item()
    if isinstance(x, np.ndarray): return x.tolist()
    return x

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--max-level', type=int, default=4)
    ap.add_argument('--out', default=os.path.join(ROOT, 'audit', 'results', 'phase5a_type_system_audit.txt'))
    args = ap.parse_args()
    os.makedirs(os.path.dirname(args.out), exist_ok=True)
    sys.stdout = Tee(args.out); T0 = time.time(); summary = {}
    print("PHASE 5a / TASK A2 -- TYPE-SYSTEM ADVERSARIAL AUDIT  (all numbers computed in this run)")
    print(f"phase-4 derivation loaded: {len(PTYPES)} panel types, {len(QTYPES)} plaquette types; keys pairwise distinct: {representatives_pairwise_distinct()}")
    print(f"tiling cross-check (phase-4 inflate vs independent tiles_at_level), levels 1-3: {[same_tiling_as_independent(m) for m in (1, 2, 3)]}")

    print("\n=== A. REPRESENTATIVES ===")
    ra = check_panel_representatives(); rq = check_plaquette_representatives(); rl = lean_certificate_reps_match()
    print(f" panel reps   : n={ra['n']} invalid={ra['invalid_config']} key_mismatch={ra['key_mismatch']} reconstruction_fail={ra['reconstruction_fail']} not_Gamma_equiv={ra['not_gamma_equivalent']} -> ok={ra['ok']}")
    print(f" plaquette reps: n={rq['n']} invalid={rq['invalid_config']} key_mismatch={rq['key_mismatch']} class_mismatch={rq['class_mismatch']} reconstruction_fail={rq['reconstruction_fail']} not_Gamma_equiv={rq['not_gamma_equivalent']} -> ok={rq['ok']}")
    print(f"   distinct tiles per plaquette representative: {rq['distinct_tiles_hist']}")
    print(f" Lean certificate data vs Python reps: {rl}")
    summary['A'] = {'panel': ra, 'plaq': rq, 'lean': rl}

    print("\n=== B. COVERAGE ===")
    cov = {}; seen_p, seen_q = set(), set()
    for m in range(1, args.max_level + 1):
        r = coverage_level(m, check_images=(m == 2)); cov[m] = r
        new_p, new_q = len(r['_panel_keys'] - seen_p), len(r['_plaq_keys'] - seen_q); seen_p |= r['_panel_keys']; seen_q |= r['_plaq_keys']
        print(f" level {m}: tiles={r['tiles']} cubes={r['cubes']} | panels={r['panels']} distinct panel keys={r['panel_types']} (new {new_p}) unknown={r['panel_unknown']} link-label conflicts={r['link_label_conflicts']}"
              f" | plaquettes={r['plaquettes']} distinct plaquette keys={r['plaq_types']} (new {new_q}) unknown={r['plaq_unknown']} class conflicts={r['class_conflicts']}")
        print(f"          class counts {r['class_counts']}  == recursion: {r['class_counts_match_recursion']};  type-resolved counts == recursion: panels {r['panel_type_counts_match_recursion']} plaquettes {r['plaq_type_counts_match_recursion']}  [{r['seconds']} s]")
        if 'image_checked_panels' in r:
            print(f"          inflation images recomputed on ALL instances: panels {r['image_checked_panels']} (mismatch {r['image_bad_panels']}), plaquettes {r['image_checked_plaqs']} (mismatch {r['image_bad_plaqs']})")
    print(f" union of keys over levels 1..{args.max_level}: {len(seen_p)} panel, {len(seen_q)} plaquette; representatives not seen: {len(PSET - seen_p)} panel, {len(QSET - seen_q)} plaquette")
    summary['B'] = {m: {k: v for k, v in r.items() if not k.startswith('_')} for m, r in cov.items()}
    summary['B']['union'] = {'panel_keys': len(seen_p), 'plaq_keys': len(seen_q), 'reps_unseen_panel': len(PSET - seen_p), 'reps_unseen_plaq': len(QSET - seen_q)}

    print("\n=== C. INVARIANCE UNDER RIGID MOTIONS ===")
    inv = invariance_test(); summary['C'] = inv
    for k in sorted(inv):
        if k != 'first_failures': print(f" {k}: {inv[k]}")
    print(f" first failures: {inv['first_failures']}")
    print(" note: the key is invariant under the 24 improper elements as well (REFL rows). This is harmless: a reflection maps")
    print("       SO(3,Z) frames to det=-1 frames, which never occur in the tiling, so on actual configurations equal key <=> related by SO(3,Z) x Z^3.")

    print("\n=== D. ORIENTATION / PATH ORDERING ===")
    d_reps = orientation_test_reps(); d_l2 = orientation_test_level(2)
    print(f" 108 representatives: {d_reps}")
    print(f" level 2, inter-tile plaquettes: {d_l2['inter_tile']}")
    print(f" level 2, all four-present plaquettes (incl. intra-tile): {d_l2['all_four_present']}")
    print(f" examples (base, i, j, labels by (start, reversed)): {d_l2['examples']}")
    summary['D'] = {'reps': d_reps, 'level2': {k: v for k, v in d_l2.items() if k != 'examples'}}

    print("\n=== E. GAUGE TRANSFORMATIONS (level 2) ===")
    g = gauge_test(2); summary['E'] = g
    print(f" tiles={g['tiles']} inter-tile links={g['inter_tile_links']} plaquettes checked={g['plaquettes_checked']} fundamental cycles={g['fundamental_cycles']}")
    for n, r in enumerate(g['rounds']): print(f" round {n}: {r}")
    print(f" classes/traces invariant: {g['ok']}; links change under gauge: {g['links_change_under_gauge']}")

    print("\n=== F. NEGATIVE CONTROLS ===")
    f1 = {m: negative_normal_reversal(m) for m in (1, 2)}
    for m, r in f1.items():
        print(f" F1 level {m}: star tile {r['star_tile']} has {r['links_incident_to_star']} incident links; baseline classes {r['baseline_class_counts']}")
        for kind, v in r['variants'].items(): print(f"    {kind:38s} {v}")
    f2 = negative_ambient_key(2); print(f" F2 (ambient / coarse keys, level 2): {f2}")
    f3 = {m: negative_boundary_convention(m) for m in (1, 2)}
    for m, r in f3.items(): print(f" F3 level {m}: {r}")
    summary['F'] = {'F1': f1, 'F2': f2, 'F3': f3}

    print("\n=== G. MISSING-NEIGHBOUR HANDLING ===")
    gres = {m: missing_neighbour_census(m) for m in range(1, min(args.max_level, 4) + 1)}
    for m, r in gres.items(): print(f" level {m}: {r}")
    sc = source_conventions(); print(f" source conventions: {sc}")
    summary['G'] = {'census': gres, 'source': sc}

    print(f"\ntotal wall time {time.time() - T0:.1f} s")
    jpath = os.path.splitext(args.out)[0] + '.json'
    with open(jpath, 'w') as fh: json.dump(jsonable(summary), fh, indent=1, default=str)
    print(f"written: {args.out}\n         {jpath}")

if __name__ == '__main__':
    main()
