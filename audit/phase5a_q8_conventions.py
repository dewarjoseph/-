"""
Phase 5a / Task A4 -- Q8 CONVENTIONS AND FREQUENCY NORMALIZATION (exact arithmetic, abstract Q8).
Run from the repository root:   python3 -u -I audit/phase5a_q8_conventions.py
Output:                          audit/results/phase5a_q8_conventions.txt  (+ .json summary)

What this module establishes (every number is recomputed at run time; nothing is pinned):

 (1) The Pauli/quaternion dictionary e_1=-i sigma_1, e_2=-i sigma_2, e_3=-i sigma_3 satisfies e_1 e_2 = e_3 (and
     the cyclic companions), the map Q8 -> SU(2) is an injective homomorphism (64 products checked with exact
     integer-valued complex matrices), and (sigma.u_a)(sigma.u_b) = -(u_a u_b)_quaternion for all 36 ordered pairs
     of signed coordinate axes.  The abstract Q8 table is DERIVED from i^2=j^2=k^2=ijk=-1 (stepwise, each step a
     one-sided multiplication) and shown UNIQUE by exhaustion over all 8^6 candidate tables.  The repository's
     integer routine src/chair44/machine_checked_certificates.py:_clifford_link_quat_int and the Lean `qmul`/
     `cliffordLink` of certificates/TypeSubstitutionCertificate.lean are compared with the derived table pair by
     pair; audit/independent_clifford_q8_audit.py's numpy `q8label` is compared as well (it agrees on every
     CLASS but its signed labels for the six non-central elements are the NEGATIVES of the quaternion dictionary,
     because it names the matrix +i sigma_m "+m" while e_m = -i sigma_m is the quaternion m).

 (2) C_ba = C_ab^{-1} (= C_ab^dagger in SU(2)) on all 48 level-1 links, and the Q8 conjugacy class of a plaquette
     Wilson loop is independent of base point and orientation (8 variants per plaquette; all level-1 and level-2
     plaquettes).

 (3) Signed labels (+i vs -i) are NOT invariants: they change under base point / orientation changes and under Q8
     gauge transformations, while conjugacy classes do not.  Under conjugation by an arbitrary SU(2) element only
     the trace survives: the Q8 element i is conjugated to -k by (1+j)/sqrt2 and out of Q8 altogether by a generic
     rotation (explicit matrices printed).  The frequencies 19/36, 13/144, 1/9, 23/144, 1/9 therefore refer to Q8
     conjugacy classes = pairs (trace, axis), where the axis is the axis of the pi-rotation Ad(W) in V4 read in the
     LOCAL frame of the base tile.  Those axis labels are meaningful only because the construction gauge-fixes the
     local frames: in the ambient gauge (spin lifts U_a) the same loop has axis M_a(axis), which depends on the base
     tile through the S3 part of M_b M_a^T (counted below), and only the trace classes {+1},{-1},{Tr=0} survive;
     the SU(2)-gauge-invariant content of the frequencies is (19/36, 13/144, 55/144).

 (4) The limiting frequencies and the finite-size normalization are reproduced from the certificate data ALONE
     (lists panelImgP, panelImgQ, plaqImg, seedPCert, seedQCert, plaqClassCert parsed from the Lean source):
     S is rebuilt, (8I - S) u = f is solved over Fractions, sum_plaquette-types u = 18, class ratios as stated;
     N_m = 18*8^m - 24*4^m + 6*2^m for m=1..6 (and 7) from the recursion v_{m+1} = S v_m + 8^m f, v_1 = f; panels
     12*(8^m - 4^m); both compared with the directly enumerated values stored in audit/results/.

 (5) STATUS OF THE FREQUENCIES.  They are not a property of the chair tiling as a point set and not a property of a
     physical system; they are invariants of one specific discrete connection modulo Q8 gauge transformations,
     i.e. of the FR30 FRAME DECORATION together with the Clifford link rule.  Changing the frame of a single tile
     by an even permutation (which leaves every cube and panel unchanged) changes the flux pattern (Phase 2 /
     End-to-end audit Section 1.4, Theorem 1.3: fundamental-cycle trace multiset {-2:1, 0:23, 2:17} ->
     {-2:1, 0:22, 2:18}); the mirror image of the tiling carries the gauge-equivalent connection sigma_1 C sigma_1
     (Phase 2 Theorem 2.4), so the frequencies are parity-invariant but still decoration-dependent.  Both facts
     are re-verified numerically below (Section 5).
"""
import os, sys, re, ast, json, time, itertools, collections, importlib.util
from fractions import Fraction as Fr
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..'))
for _p in (ROOT, HERE):
    if _p not in sys.path:
        sys.path.insert(0, _p)
RESULTS = os.path.join(HERE, 'results')
LEAN = os.path.join(ROOT, 'certificates', 'TypeSubstitutionCertificate.lean')


def _load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec); spec.loader.exec_module(mod)
    return mod


IA = _load('independent_clifford_q8_audit', os.path.join(HERE, 'independent_clifford_q8_audit.py'))

# =====================================================================================================================
# 0. Abstract Q8 = {+-1, +-i, +-j, +-k}; element = (sign, basis letter)
# =====================================================================================================================
BASIS = ('1', 'i', 'j', 'k')
ONE, MONE = (1, '1'), (-1, '1')


def derive_q8_table():
    """Derive the 4x4 basis-product table from i^2 = j^2 = k^2 = ijk = -1 with -1 central, (-1)^2 = 1.
    Returns (table, steps).  table[(x, y)] = (sign, basis) for x, y in BASIS.  Each step multiplies an established
    equation on one side by a generator and uses associativity plus the defining relations only."""
    tab = {}
    for b in BASIS:
        tab[('1', b)] = (1, b); tab[(b, '1')] = (1, b)
    for b in 'ijk':
        tab[(b, b)] = MONE
    steps = []
    # (ij)k = -1  --right-multiply by k-->  (ij)(kk) = -k  -->  (ij)(-1) = -k  -->  ij = k
    tab[('i', 'j')] = (1, 'k'); steps.append("ijk=-1, right-multiply by k: (ij)(k k)=(ij)(-1)=-k  =>  ij = k")
    # ij = k  --left-multiply by i-->  (ii)j = ik  -->  -j = ik
    tab[('i', 'k')] = (-1, 'j'); steps.append("ij=k, left-multiply by i: (i i)j = -j = ik  =>  ik = -j")
    # ij = k  --right-multiply by j-->  i(jj) = kj  -->  -i = kj
    tab[('k', 'j')] = (-1, 'i'); steps.append("ij=k, right-multiply by j: i(j j) = -i = kj  =>  kj = -i")
    # ijk = -1 --left-multiply by i--> (ii)(jk) = -i --> -(jk) = -i --> jk = i
    tab[('j', 'k')] = (1, 'i'); steps.append("ijk=-1, left-multiply by i: (i i)(jk) = -(jk) = -i  =>  jk = i")
    # jk = i --left-multiply by j--> (jj)k = ji --> -k = ji
    tab[('j', 'i')] = (-1, 'k'); steps.append("jk=i, left-multiply by j: (j j)k = -k = ji  =>  ji = -k")
    # jk = i --right-multiply by i--> j(ki) = ii = -1 --left-multiply by j--> (jj)(ki) = -j --> ki = j
    tab[('k', 'i')] = (1, 'j'); steps.append("jk=i, right-multiply by i: j(ki) = i i = -1; left-multiply by j: -(ki) = -j  =>  ki = j")
    return tab, steps


Q8TAB, Q8STEPS = derive_q8_table()
Q8 = [(s, b) for s in (1, -1) for b in BASIS]


def mul(a, b, tab=Q8TAB):
    s, c = tab[(a[1], b[1])]
    return (a[0] * b[0] * s, c)


def inv(a):
    return a if a[1] == '1' else (-a[0], a[1])


def neg(a):
    return (-a[0], a[1])


def cls(a):
    """Q8 conjugacy class: '1', '-1', 'i', 'j', 'k'  (classes {+1},{-1},{+-i},{+-j},{+-k})."""
    return ('1' if a[0] > 0 else '-1') if a[1] == '1' else a[1]


def lab(a):
    return ('+' if a[0] > 0 else '-') + a[1]


def q8_group_axioms(tab=Q8TAB):
    """Closure, associativity (512 triples), identity, inverses, relations, centre, class structure."""
    def m(a, b): return mul(a, b, tab)
    rel = (m((1, 'i'), (1, 'i')) == MONE and m((1, 'j'), (1, 'j')) == MONE and m((1, 'k'), (1, 'k')) == MONE
           and m(m((1, 'i'), (1, 'j')), (1, 'k')) == MONE)
    closed = all(m(a, b) in Q8 for a in Q8 for b in Q8)
    assoc = all(m(m(a, b), c) == m(a, m(b, c)) for a in Q8 for b in Q8 for c in Q8)
    ident = all(m(ONE, a) == a == m(a, ONE) for a in Q8)
    inverses = all(m(a, inv(a)) == ONE == m(inv(a), a) for a in Q8)
    centre = sorted(a for a in Q8 if all(m(a, b) == m(b, a) for b in Q8))
    classes = {}
    for a in Q8:
        classes[a] = frozenset(m(m(g, a), inv(g)) for g in Q8)
    ncl = len(set(classes.values()))
    cls_ok = all(classes[a] == frozenset(x for x in Q8 if cls(x) == cls(a)) for a in Q8)
    inv_closed = all(cls(inv(a)) == cls(a) for a in Q8)
    return dict(relations=rel, closed=closed, associative=assoc, identity=ident, inverses=inverses,
                centre=centre, n_classes=ncl, class_function_matches_orbits=cls_ok, classes_closed_under_inversion=inv_closed)


def q8_uniqueness_by_exhaustion():
    """All tables on {+-1,+-i,+-j,+-k} with -1 central, i^2=j^2=k^2=-1, products of distinct generators free in Q8,
    that satisfy ijk=-1 and associativity on the 27 generator triples.  Expected: exactly one (the derived table)."""
    nonid = ('i', 'j', 'k')
    pairs = [(x, y) for x in nonid for y in nonid if x != y]
    found = []
    base = {}
    for b in BASIS:
        base[('1', b)] = (1, b); base[(b, '1')] = (1, b)
    for b in nonid:
        base[(b, b)] = MONE
    gens = [(1, b) for b in nonid]
    for choice in itertools.product(Q8, repeat=6):
        tab = dict(base)
        for (x, y), v in zip(pairs, choice):
            tab[(x, y)] = v
        def m(a, b):
            s, c = tab[(a[1], b[1])]
            return (a[0] * b[0] * s, c)
        if m(m(gens[0], gens[1]), gens[2]) != MONE:
            continue
        ok = True
        for a in gens:
            for b in gens:
                for c in gens:
                    if m(m(a, b), c) != m(a, m(b, c)):
                        ok = False; break
                if not ok: break
            if not ok: break
        if ok:
            found.append(dict(tab))
    return found


# =====================================================================================================================
# 1. Pauli / quaternion dictionary with exact integer-valued complex matrices
# =====================================================================================================================
SIG = [np.array([[0, 1], [1, 0]], complex), np.array([[0, -1j], [1j, 0]], complex), np.array([[1, 0], [0, -1]], complex)]
I2 = np.eye(2, dtype=complex)
E = [-1j * S for S in SIG]                       # e_m = -i sigma_m
PHI = {(1, '1'): I2, (-1, '1'): -I2}
for _m, _b in enumerate('ijk'):
    PHI[(1, _b)] = E[_m]; PHI[(-1, _b)] = -E[_m]


def phi(q):
    return PHI[q]


def phi_inv(M):
    """Exact identification of a 2x2 matrix with a Q8 element (entries are in {0,+-1,+-i}; comparisons are exact)."""
    for q, mat in PHI.items():
        if np.array_equal(M, mat):
            return q
    return None


def sdot(u):
    return sum(int(u[m]) * SIG[m] for m in range(3))


AXES = [np.array(v, dtype=int) for v in ((1, 0, 0), (-1, 0, 0), (0, 1, 0), (0, -1, 0), (0, 0, 1), (0, 0, -1))]


def vec_q(u):
    """signed coordinate axis -> pure quaternion (sign, letter)"""
    (m,) = np.nonzero(u)[0]
    assert abs(int(u[m])) == 1 and sum(abs(int(x)) for x in u) == 1
    return (int(u[m]), 'ijk'[m])


def link_q8(Ma, Mb, n):
    """C_ab = (sigma.u_a)(sigma.u_b) = -(u_a u_b)_quaternion with u_a = M_a^T n, u_b = M_b^T n (exact Q8)."""
    ua = Ma.T @ n; ub = Mb.T @ n
    return neg(mul(vec_q(ua), vec_q(ub)))


def repo_quat_to_q8(t):
    s, x, y, z = (int(v) for v in t)
    nz = [(v, b) for v, b in zip((s, x, y, z), BASIS) if v != 0]
    assert len(nz) == 1 and abs(nz[0][0]) == 1, t
    return (nz[0][0], nz[0][1])


def check_dictionary():
    out = {}
    out['e1e2=e3'] = bool(np.array_equal(E[0] @ E[1], E[2]))
    out['e2e3=e1'] = bool(np.array_equal(E[1] @ E[2], E[0]))
    out['e3e1=e2'] = bool(np.array_equal(E[2] @ E[0], E[1]))
    out['em^2=-1'] = all(np.array_equal(E[m] @ E[m], -I2) for m in range(3))
    out['e1e2e3=-1'] = bool(np.array_equal(E[0] @ E[1] @ E[2], -I2))
    out['phi_homomorphism_64'] = all(np.array_equal(phi(a) @ phi(b), phi(mul(a, b))) for a in Q8 for b in Q8)
    out['phi_injective'] = len({phi(a).tobytes() for a in Q8}) == 8
    out['phi_in_SU2'] = all(np.array_equal(phi(a) @ phi(a).conj().T, I2) and abs(np.linalg.det(phi(a)) - 1) < 1e-12 for a in Q8)
    # 36 ordered pairs of signed axes
    rows = []; n_pauli_ok = n_repo_ok = n_numpy_class_ok = n_numpy_label_ok = 0
    repo_disagree, numpy_label_disagree = [], []
    from src.chair44.machine_checked_certificates import _clifford_link_quat_int
    for ua in AXES:
        for ub in AXES:
            M = sdot(ua) @ sdot(ub)
            q_mat = phi_inv(M)
            q_abs = neg(mul(vec_q(ua), vec_q(ub)))
            pauli_ok = (q_mat == q_abs)
            q_repo = repo_quat_to_q8(_clifford_link_quat_int(ua, ub))
            repo_ok = (q_repo == q_abs)
            Mnp = IA.sdot(ua) @ IA.sdot(ub); lbl = IA.q8label(Mnp)
            lbl_class = {'+1': '1', '-1': '-1'}.get(lbl, lbl[1:])          # class named by the q8label string
            numpy_class_ok = (phi_inv(Mnp) == q_abs) and (lbl_class == cls(q_abs))
            numpy_label_ok = (lbl == lab(q_abs))
            n_pauli_ok += pauli_ok; n_repo_ok += repo_ok; n_numpy_class_ok += numpy_class_ok; n_numpy_label_ok += numpy_label_ok
            tua, tub = tuple(int(x) for x in ua), tuple(int(x) for x in ub)
            if not repo_ok: repo_disagree.append((tua, tub, lab(q_abs), lab(q_repo)))
            if not numpy_label_ok: numpy_label_disagree.append((tua, tub, lab(q_abs), lbl))
            rows.append((tuple(int(x) for x in ua), tuple(int(x) for x in ub), lab(q_abs), lab(q_repo), lbl))
    out['pairs'] = rows
    out['n_pairs'] = len(rows)
    out['pauli_equals_minus_quaternion_product'] = n_pauli_ok
    out['repo_int_routine_agrees'] = n_repo_ok
    out['repo_int_routine_disagreements'] = repo_disagree
    out['numpy_q8label_class_agrees'] = n_numpy_class_ok
    out['numpy_q8label_signed_agrees'] = n_numpy_label_ok
    out['numpy_q8label_signed_disagreements'] = numpy_label_disagree
    # the sign-flip pattern of q8label: '+m' names +i sigma_m = -e_m
    out['q8label_plus_m_is_matrix_i_sigma_m'] = all(IA.q8label(1j * SIG[m]) == '+' + 'ijk'[m] for m in range(3))
    out['i_sigma_m_is_quaternion_minus_m'] = all(phi_inv(1j * SIG[m]) == (-1, 'ijk'[m]) for m in range(3))
    return out


def lean_qmul_check():
    """Translate the Lean `qmul` body to Python and compare with the derived table on all 64 Q8 products."""
    src = open(LEAN).read()
    body = src.split('def qmul (a b : Q) : Q :=')[1].split('def qOne')[0]
    body = body.replace('⟨', '(').replace('⟩', ')')
    for v in 'ab':
        for comp, idx in zip('sxyz', range(4)):
            body = body.replace(f'{v}.{comp}', f'{v}[{idx}]')
    assert re.fullmatch(r'[\sab\[\]0-3+*,()-]+', body), body
    f = eval('lambda a, b: ' + body.strip())
    def to4(q):
        v = [0, 0, 0, 0]; v[BASIS.index(q[1])] = q[0]; return tuple(v)
    ok = all(tuple(f(to4(a), to4(b))) == to4(mul(a, b)) for a in Q8 for b in Q8)
    # Lean cliffordLink = negated qmul of the two pure quaternions: same formula as link_q8 by construction
    return ok, body.strip()


# =====================================================================================================================
# 2. Level-1 links, reverse normal, plaquette Wilson loops (8 variants)
# =====================================================================================================================
def level_data(level):
    tiles = IA.tiles_at_level(IA.FR30, level)
    owner, edges = IA.panel_edges(tiles)
    return tiles, owner, edges


def check_links_level1():
    tiles, owner, edges = level_data(1)
    from src.chair44.machine_checked_certificates import _clifford_link_quat_int
    n_inv = n_dag = n_repo = n_numpy = 0
    counts = collections.Counter()
    for a, b, n, _, _ in edges:
        Ma, Mb = tiles[a][0], tiles[b][0]
        Cab = link_q8(Ma, Mb, n); Cba = link_q8(Mb, Ma, -n)
        n_inv += (Cba == inv(Cab))
        n_dag += bool(np.array_equal(phi(Cba), phi(Cab).conj().T))
        n_repo += (repo_quat_to_q8(_clifford_link_quat_int(Ma.T @ n, Mb.T @ n)) == Cab)
        n_numpy += (phi_inv(IA.clifford_link(Ma, Mb, n)) == Cab)
        counts[cls(Cab)] += 1
    return dict(n_links=len(edges), reverse_normal_is_inverse=n_inv, reverse_normal_is_dagger=n_dag,
                repo_int_routine_agrees=n_repo, numpy_matrix_agrees=n_numpy, link_classes=dict(counts))


EI = [np.array(v, dtype=int) for v in ((1, 0, 0), (0, 1, 0), (0, 0, 1))]


def plaquettes_of(owner):
    cubes = set(owner)
    out = []
    for c in sorted(cubes):
        c = np.array(c, dtype=int)
        for (i, j) in ((0, 1), (0, 2), (1, 2)):
            cs = [tuple(c), tuple(c + EI[i]), tuple(c + EI[i] + EI[j]), tuple(c + EI[j])]
            if all(x in cubes for x in cs):
                out.append(cs)
    return out


def link_cubes(tiles, owner, c1, c2, links=None):
    a, b = owner[c1], owner[c2]
    if a == b:
        return ONE
    n = np.array(c2, dtype=int) - np.array(c1, dtype=int)
    if links is not None:
        return links[(a, b, tuple(int(x) for x in n))]
    return link_q8(tiles[a][0], tiles[b][0], n)


def holonomy(tiles, owner, seq, links=None):
    W = ONE
    for q in range(4):
        W = mul(W, link_cubes(tiles, owner, seq[q], seq[(q + 1) % 4], links))
    return W


def variants(cs):
    for order in (cs, cs[::-1]):
        for start in range(4):
            yield order[start:] + order[:start]


def check_plaquette_invariance(level):
    tiles, owner, edges = level_data(level)
    plaqs = plaquettes_of(owner)
    n_inter = 0; n_class_ok = 0; n_label_varies = 0; examples = []
    class_counts = collections.Counter(); label_counts = collections.Counter()
    for cs in plaqs:
        inter = len({owner[x] for x in cs}) > 1
        Ws = [holonomy(tiles, owner, seq) for seq in variants(cs)]
        classes = {cls(W) for W in Ws}; labels = {lab(W) for W in Ws}
        if len(classes) == 1: n_class_ok += 1
        if inter:
            n_inter += 1
            class_counts[cls(Ws[0])] += 1; label_counts[lab(Ws[0])] += 1
            if len(labels) > 1:
                n_label_varies += 1
                if len(examples) < 2:
                    examples.append(dict(cubes=[list(map(int, x)) for x in cs], tiles=[int(owner[x]) for x in cs],
                                         labels_of_8_variants=[lab(W) for W in Ws], classes=sorted(classes)))
        else:
            assert all(W == ONE for W in Ws)
    return dict(level=level, n_plaquettes=len(plaqs), n_inter_tile=n_inter, n_class_independent_of_basepoint_orientation=n_class_ok,
                n_inter_tile_with_varying_signed_label=n_label_varies, inter_tile_class_counts=dict(class_counts),
                inter_tile_signed_label_counts_base_cube0=dict(label_counts), examples=examples)


# =====================================================================================================================
# 3. Group element vs gauge-invariant holonomy
# =====================================================================================================================
def check_q8_gauge(level=1, seed=20261021):
    tiles, owner, edges = level_data(level)
    plaqs = [cs for cs in plaquettes_of(owner) if len({owner[x] for x in cs}) > 1]
    rng = np.random.RandomState(seed)
    G = {a: Q8[int(rng.randint(8))] for a in range(len(tiles))}
    links0, links1 = {}, {}
    for a, b, n, _, _ in edges:
        C = link_q8(tiles[a][0], tiles[b][0], n)
        links0[(a, b, tuple(int(x) for x in n))] = C
        links0[(b, a, tuple(int(-x) for x in n))] = inv(C)
        links1[(a, b, tuple(int(x) for x in n))] = mul(mul(G[a], C), inv(G[b]))
        links1[(b, a, tuple(int(-x) for x in n))] = mul(mul(G[b], inv(C)), inv(G[a]))
    n_cls_eq = n_lab_eq = 0; example = None
    for cs in plaqs:
        W0 = holonomy(tiles, owner, cs, links0); W1 = holonomy(tiles, owner, cs, links1)
        a0 = owner[cs[0]]
        assert W1 == mul(mul(G[a0], W0), inv(G[a0]))
        n_cls_eq += (cls(W0) == cls(W1)); n_lab_eq += (W0 == W1)
        if example is None and W0 != W1:
            example = dict(cubes=[list(map(int, x)) for x in cs], base_tile=int(a0), gauge_at_base=lab(G[a0]), before=lab(W0), after=lab(W1))
    return dict(level=level, n_inter_tile=len(plaqs), gauge=[lab(G[a]) for a in sorted(G)], classes_equal=n_cls_eq,
                signed_labels_equal=n_lab_eq, example=example)


def check_su2_conjugation():
    """Q8 classes are not SU(2)-conjugation invariants; only Tr is.  (a) exact: U=(1+j)/sqrt2 maps i -> -k.
    (b) generic rotation maps i outside Q8."""
    out = {}
    Uy = (I2 + E[1]) / np.sqrt(2)                      # (1 + j)/sqrt2 = exp(-i pi/4 sigma_2)
    X = Uy @ E[0] @ Uy.conj().T
    Xr = np.rint(X.real) + 1j * np.rint(X.imag)
    assert np.allclose(X, Xr, atol=1e-12)
    q = phi_inv(Xr)
    out['U=(1+j)/sqrt2'] = dict(image_of_i=lab(q) if q else None, class_before='i', class_after=cls(q) if q else None,
                               trace_before=int(np.rint(np.trace(E[0]).real)), trace_after=int(np.rint(np.trace(X).real)))
    # generic SU(2) element: rotation by 1 rad about (1,2,3)/sqrt14
    nvec = np.array([1.0, 2.0, 3.0]) / np.sqrt(14.0); th = 1.0
    U = np.cos(th / 2) * I2 - 1j * np.sin(th / 2) * sdot_f(nvec)
    Y = U @ E[0] @ U.conj().T
    dist = min(np.linalg.norm(Y - phi(a)) for a in Q8)
    out['generic_U'] = dict(rotation='1 rad about (1,2,3)/sqrt14', image_matrix=[[complex(Y[r, c]) for c in range(2)] for r in range(2)],
                            min_frobenius_distance_to_Q8=float(dist), trace=complex(np.trace(Y)), in_Q8=bool(dist < 1e-9))
    # the stabiliser in SU(2) of all three non-central classes is Q8 itself (Ad(U) must fix each axis up to sign)
    return out


def sdot_f(u):
    return sum(float(u[m]) * SIG[m] for m in range(3))


def spin_lift(M):
    """U in SU(2) with U (sigma.v) U^dag = sigma.(M v) for M in SO(3) (Shepperd), verified by assertion."""
    M = np.asarray(M, dtype=float); t = np.trace(M)
    if t > 0:
        r = np.sqrt(1 + t); w = 0.5 * r
        x = (M[2, 1] - M[1, 2]) / (2 * r); y = (M[0, 2] - M[2, 0]) / (2 * r); z = (M[1, 0] - M[0, 1]) / (2 * r)
    else:
        i = int(np.argmax(np.diag(M))); j = (i + 1) % 3; k = (i + 2) % 3
        r = np.sqrt(1 + M[i, i] - M[j, j] - M[k, k]); q = [0.0, 0.0, 0.0]
        q[i] = 0.5 * r; w = (M[k, j] - M[j, k]) / (2 * r); q[j] = (M[j, i] + M[i, j]) / (2 * r); q[k] = (M[k, i] + M[i, k]) / (2 * r)
        x, y, z = q
    U = w * I2 - 1j * (x * SIG[0] + y * SIG[1] + z * SIG[2])
    for v in np.eye(3):
        assert np.allclose(U @ sdot_f(v) @ U.conj().T, sdot_f(M @ v), atol=1e-12)
    return U


def check_ambient_relabeling(level):
    """Local-frame axis label (the certified class) vs ambient axis M_a(axis) in the spin-lift gauge."""
    tiles, owner, edges = level_data(level)
    plaqs = [cs for cs in plaquettes_of(owner) if len({owner[x] for x in cs}) > 1]
    local = collections.Counter(); ambient_base0 = collections.Counter(); n_ambient_basepoint_dependent = 0
    n_spinlift_checked = 0; n_spinlift_ok = 0; example = None
    lifts = {a: spin_lift(tiles[a][0]) for a in range(len(tiles))} if level == 1 else None
    for cs in plaqs:
        W = holonomy(tiles, owner, cs)
        c = cls(W); local[c] += 1
        if W[1] == '1':
            ambient_base0[c] += 1; continue
        m = 'ijk'.index(W[1])
        amb = []
        for start in range(4):
            seq = cs[start:] + cs[:start]
            Ws = holonomy(tiles, owner, seq)
            assert cls(Ws) == c
            a = owner[seq[0]]
            v = tiles[a][0] @ EI['ijk'.index(Ws[1])]
            (ax,) = np.nonzero(v)[0]
            amb.append('xyz'[int(ax)])
        ambient_base0[amb[0]] += 1
        if len(set(amb)) > 1:
            n_ambient_basepoint_dependent += 1
            if example is None:
                example = dict(cubes=[list(map(int, x)) for x in cs], base_tiles=[int(owner[x]) for x in cs], local_class=c, ambient_axis_per_base_tile=amb)
        if lifts is not None:
            a0 = owner[cs[0]]; Wa = lifts[a0] @ phi(W) @ lifts[a0].conj().T
            n_spinlift_checked += 1
            n_spinlift_ok += bool(np.allclose(Wa, 1j * SIG['xyz'.index(amb[0])], atol=1e-9) or np.allclose(Wa, -1j * SIG['xyz'.index(amb[0])], atol=1e-9))
    return dict(level=level, n_inter_tile=len(plaqs), local_frame_classes=dict(local), ambient_axis_classes_base_cube0=dict(ambient_base0),
                n_ambient_axis_depends_on_base_tile=n_ambient_basepoint_dependent, spinlift_numeric_checked=n_spinlift_checked,
                spinlift_numeric_ok=n_spinlift_ok, example=example)


# =====================================================================================================================
# 4. Certificate data -> exact limits and normalization
# =====================================================================================================================
def parse_lean_lists(path=LEAN):
    src = open(path).read()
    out = {}
    for name in ('panelImgP', 'panelImgQ', 'plaqImg', 'plaqClassCert', 'seedPCert', 'seedQCert', 'W8L'):
        m = re.search(r'^def %s : List [^:]+ := (\[.*\])\s*$' % name, src, re.M)
        assert m, name
        lit = m.group(1)
        assert re.fullmatch(r'[\[\]\d,\s-]+', lit), name
        out[name] = ast.literal_eval(lit)
    m = re.search(r'^def D : Int := (\d+)\s*$', src, re.M); out['D'] = int(m.group(1))
    return out


def solve_fraction(A, b):
    """Exact Gaussian elimination with partial (nonzero) pivoting over Fractions.  A: list of lists, b: list."""
    n = len(A); M = [row[:] + [bi] for row, bi in zip(A, b)]
    for col in range(n):
        piv = next(r for r in range(col, n) if M[r][col] != 0)
        M[col], M[piv] = M[piv], M[col]
        p = M[col][col]
        M[col] = [x / p for x in M[col]]
        for r in range(n):
            if r != col and M[r][col] != 0:
                f = M[r][col]
                M[r] = [x - f * y for x, y in zip(M[r], M[col])]
    return [M[r][n] for r in range(n)]


def certificate_limits(data):
    P, PQ, QQ = data['panelImgP'], data['panelImgQ'], data['plaqImg']
    nP, nQ = len(P), len(QQ); N = nP + nQ
    assert all(len(l) == 4 for l in P) and all(len(l) == 4 for l in PQ) and all(len(l) == 2 for l in QQ)
    S = [[0] * N for _ in range(N)]
    for c in range(nP):
        for r in P[c]: S[r][c] += 1
        for r in PQ[c]: S[nP + r][c] += 1
    for c in range(nQ):
        for r in QQ[c]: S[nP + r][nP + c] += 1
    f = list(data['seedPCert']) + list(data['seedQCert'])
    assert len(f) == N and sum(data['seedPCert']) == 48 and sum(data['seedQCert']) == 60
    A = [[Fr(8 if r == c else 0) - Fr(S[r][c]) for c in range(N)] for r in range(N)]
    u = solve_fraction(A, [Fr(x) for x in f])
    # verify the solution exactly
    assert all(sum(A[r][c] * u[c] for c in range(N)) == Fr(f[r]) for r in range(N))
    classes = data['plaqClassCert']; names = ['1', '-1', 'i', 'j', 'k']
    tot = sum(u[nP:])
    class_u = {names[k]: sum(u[nP + q] for q in range(nQ) if classes[q] == k) for k in range(5)}
    freqs = {k: v / tot for k, v in class_u.items()}
    D = data['D']; W8 = data['W8L']
    w8_match = all(Fr(W8[r], D) == u[r] for r in range(N))
    # recursion with Python integers: v_1 = f, v_{m+1} = S v_m + 8^m f
    def Sv(v): return [sum(S[r][c] * v[c] for c in range(N)) for r in range(N)]
    v = {1: list(f)}
    for m in range(1, 7):
        sv = Sv(v[m]); v[m + 1] = [sv[r] + 8 ** m * f[r] for r in range(N)]
    rec = {}
    for m in range(1, 8):
        plq = sum(v[m][nP:]); pan = sum(v[m][:nP])
        cc = {names[k]: sum(v[m][nP + q] for q in range(nQ) if classes[q] == k) for k in range(5)}
        rec[m] = dict(panels=pan, plaquettes=plq, classes=cc,
                      plaquette_formula=18 * 8 ** m - 24 * 4 ** m + 6 * 2 ** m, panel_formula=12 * (8 ** m - 4 ** m))
    # exact closed form consistency: v_m - 8^m u must decay like 4^m: check (v_m - 8^m u) = S^{m-1}(f - 8u) exactly
    w = [Fr(f[r]) - 8 * u[r] for r in range(N)]
    cf_ok = True
    for m in range(1, 8):
        cf_ok &= all(Fr(v[m][r]) - 8 ** m * u[r] == w[r] for r in range(N))
        w = [sum(Fr(S[r][c]) * w[c] for c in range(N)) for r in range(N)]
    return dict(nP=nP, nQ=nQ, N=N, column_sums_panels=sorted(set(sum(S[r][c] for r in range(N)) for c in range(nP))),
                column_sums_plaquettes=sorted(set(sum(S[r][c] for r in range(N)) for c in range(nP, N))),
                lim_N_over_8m=tot, class_u=class_u, freqs=freqs, trace0_freq=freqs['i'] + freqs['j'] + freqs['k'],
                W8_over_D_equals_u=w8_match, recursion=rec, residual_identity_ok=cf_ok,
                lim_panels_over_8m=sum(u[:nP]))


def read_direct_counts():
    """Directly enumerated inter-tile plaquette / panel counts stored in audit/results (read, not recomputed)."""
    out = {}
    p = os.path.join(RESULTS, 'phase5a_independent_enumerator.txt')
    if os.path.exists(p):
        lvl = None; d = {}
        for line in open(p):
            m = re.match(r'LEVEL (\d+):', line)
            if m: lvl = int(m.group(1)); continue
            m = re.search(r'plaquettes: total=(\d+) inter-tile=(\d+)', line)
            if m and lvl: d.setdefault(lvl, {})['inter_tile'] = int(m.group(2)); d[lvl]['total'] = int(m.group(1))
            m = re.search(r'inter-tile classes: (\{.*\})', line)
            if m and lvl: d.setdefault(lvl, {})['classes'] = ast.literal_eval(m.group(1))
            m = re.search(r'panels: shared unit faces=(\d+)', line)
            if m and lvl: d.setdefault(lvl, {})['panels'] = int(m.group(1))
        out['phase5a_independent_enumerator.txt'] = d
    p = os.path.join(RESULTS, 'phase3_plaquette_recursion_levels1-5.txt')
    if os.path.exists(p):
        d = {}
        for line in open(p):
            m = re.match(r'level (\d+): plaquettes=(\d+) inter-tile N_k=(\d+)', line)
            if m: d[int(m.group(1))] = dict(total=int(m.group(2)), inter_tile=int(m.group(3)))
        out['phase3_plaquette_recursion_levels1-5.txt'] = d
    p = os.path.join(RESULTS, 'phase5a_type_system_audit.txt')
    if os.path.exists(p):
        d = {}
        for line in open(p):
            m = re.search(r'level (\d+): tiles=(\d+) cubes=(\d+) \| panels=(\d+) .*\| plaquettes=(\d+)', line)
            if m: d[int(m.group(1))] = dict(panels=int(m.group(4)), inter_tile=int(m.group(5)))
        out['phase5a_type_system_audit.txt'] = d
    return out


# =====================================================================================================================
# 5. Decoration dependence (Theorem 1.3 counterexample) and mirror invariance (Theorem 2.4), re-verified
# =====================================================================================================================
def check_decoration_dependence_and_mirror():
    tiles, owner, edges = level_data(1)
    plaqs = [cs for cs in plaquettes_of(owner) if len({owner[x] for x in cs}) > 1]
    base = collections.Counter(cls(holonomy(tiles, owner, cs)) for cs in plaqs)
    # change frame of tile 3 by the even permutation (1 2 0): same cubes, same panels, different frames
    R = IA.perm_mat((1, 2, 0)); assert round(np.linalg.det(R)) == 1
    tiles_mod = list(tiles); G0, T0, c0 = tiles_mod[3]; tiles_mod[3] = (G0 @ R, T0, c0)
    assert tiles_mod[3][2] == tiles[3][2]
    mod = collections.Counter(cls(holonomy(tiles_mod, owner, cs)) for cs in plaqs)
    # fundamental-cycle trace multisets as in the audit (numpy, Phase 2 convention)
    links0 = [IA.clifford_link(tiles[a][0], tiles[b][0], n) for a, b, n, _, _ in edges]
    links1 = [IA.clifford_link(tiles_mod[a][0], tiles_mod[b][0], n) for a, b, n, _, _ in edges]
    tr0 = sorted(collections.Counter(int(round(np.trace(h).real)) for h in IA.fundamental_cycle_holonomies(len(tiles), edges, links0)).items())
    tr1 = sorted(collections.Counter(int(round(np.trace(h).real)) for h in IA.fundamental_cycle_holonomies(len(tiles), edges, links1)).items())
    # mirror: P = diag(-1,1,1); frames P M P; cubes c -> P c - e_1; links become sigma_1 C sigma_1 on corresponding panels
    Pm = np.diag([-1, 1, 1])
    n_mirror_ok = 0
    for a, b, n, ca, cb in edges:
        C = phi(link_q8(tiles[a][0], tiles[b][0], n))
        Cm = phi(link_q8(Pm @ tiles[a][0] @ Pm, Pm @ tiles[b][0] @ Pm, Pm @ n))
        n_mirror_ok += bool(np.array_equal(Cm, SIG[0] @ C @ SIG[0]))
    tiles_m = [(Pm @ G @ Pm, T, frozenset(tuple((Pm @ np.array(c)) - np.array([1, 0, 0])) for c in cs)) for G, T, cs in tiles]
    owner_m = {c: a for a, (_, _, cs) in enumerate(tiles_m) for c in cs}
    plaqs_m = [cs for cs in plaquettes_of(owner_m) if len({owner_m[x] for x in cs}) > 1]
    mirror = collections.Counter(cls(holonomy(tiles_m, owner_m, cs)) for cs in plaqs_m)
    return dict(level1_plaquette_classes=dict(base), tile3_frame_times_perm120_classes=dict(mod), classes_changed=(base != mod),
                fundamental_cycle_traces_before=tr0, fundamental_cycle_traces_after=tr1,
                mirror_links_equal_sigma1_C_sigma1=n_mirror_ok, n_links=len(edges), mirror_plaquette_classes=dict(mirror),
                mirror_classes_equal=(mirror == base))


# =====================================================================================================================
def main():
    t0 = time.time(); os.makedirs(RESULTS, exist_ok=True)
    out_txt = os.path.join(RESULTS, 'phase5a_q8_conventions.txt'); out_json = os.path.join(RESULTS, 'phase5a_q8_conventions.json')
    lines = []; summary = {}
    def P(*a):
        s = ' '.join(str(x) for x in a); print(s); lines.append(s)

    P("PHASE 5a / TASK A4 -- Q8 CONVENTIONS AND FREQUENCY NORMALIZATION (all numbers computed in this run)")
    P("=" * 100); P("0. ABSTRACT Q8 DERIVED FROM i^2 = j^2 = k^2 = ijk = -1  (-1 central, (-1)^2 = 1)")
    for s in Q8STEPS: P("   " + s)
    P("   basis table:", {f"{x}{y}": lab(Q8TAB[(x, y)]) for x in 'ijk' for y in 'ijk' if x != y})
    ax = q8_group_axioms(); P("   group axioms / structure:", ax)
    found = q8_uniqueness_by_exhaustion()
    uniq = len(found) == 1 and all(found[0][k] == Q8TAB[k] for k in found[0])
    P(f"   exhaustive search over 8^6 = {8**6} candidate tables: {len(found)} satisfy ijk=-1 + associativity; equals derived table: {uniq}")
    summary['q8'] = dict(axioms={k: (v if not isinstance(v, list) else [lab(x) for x in v]) for k, v in ax.items()}, unique_table=uniq, n_candidates=8 ** 6, n_valid=len(found))

    P(""); P("=" * 100); P("1. PAULI / QUATERNION DICTIONARY  e_m = -i sigma_m")
    d = check_dictionary()
    for k in ('e1e2=e3', 'e2e3=e1', 'e3e1=e2', 'em^2=-1', 'e1e2e3=-1', 'phi_homomorphism_64', 'phi_injective', 'phi_in_SU2'):
        P(f"   {k}: {d[k]}")
    P(f"   (sigma.u_a)(sigma.u_b) == -(u_a u_b)_quat on {d['pauli_equals_minus_quaternion_product']}/{d['n_pairs']} ordered signed-axis pairs")
    P(f"   repo _clifford_link_quat_int agrees on {d['repo_int_routine_agrees']}/{d['n_pairs']} pairs; disagreements: {d['repo_int_routine_disagreements']}")
    P(f"   independent-audit numpy q8label: CLASS agrees on {d['numpy_q8label_class_agrees']}/{d['n_pairs']}; SIGNED label agrees on {d['numpy_q8label_signed_agrees']}/{d['n_pairs']}")
    P(f"   reason: q8label names +i sigma_m as '+m' ({d['q8label_plus_m_is_matrix_i_sigma_m']}) but +i sigma_m = -e_m = quaternion -m ({d['i_sigma_m_is_quaternion_minus_m']});")
    P(f"   so q8label's signs of the six non-central elements are the negatives of the quaternion dictionary (first 6 disagreements): {d['numpy_q8label_signed_disagreements'][:6]}")
    P("   table of all 36 pairs (u_a, u_b, quaternion C, repo C, numpy q8label):")
    for r in d['pairs']: P("     ", r)
    lq_ok, lq_body = lean_qmul_check(); P(f"   Lean qmul (translated: {lq_body}) == derived table on 64 products: {lq_ok}")
    summary['dictionary'] = {k: v for k, v in d.items() if k != 'pairs'}; summary['lean_qmul_matches'] = lq_ok

    P(""); P("=" * 100); P("2. LEVEL-1 LINKS AND PLAQUETTE WILSON LOOPS")
    L = check_links_level1(); P("   links:", L)
    pl = {}
    for lvl in (1, 2):
        r = check_plaquette_invariance(lvl); pl[lvl] = r
        P(f"   level {lvl}: plaquettes={r['n_plaquettes']} inter-tile={r['n_inter_tile']}; class independent of base point & orientation (8 variants): {r['n_class_independent_of_basepoint_orientation']}/{r['n_plaquettes']}")
        P(f"            inter-tile with varying SIGNED label across the 8 variants: {r['n_inter_tile_with_varying_signed_label']}/{r['n_inter_tile']}")
        P(f"            inter-tile class counts: {r['inter_tile_class_counts']}; signed labels at base cube 0, forward orientation: {r['inter_tile_signed_label_counts_base_cube0']}")
    summary['links_level1'] = L; summary['plaquettes'] = pl

    P(""); P("=" * 100); P("3. GROUP ELEMENT vs GAUGE-INVARIANT HOLONOMY")
    for ex in pl[1]['examples']: P("   base-point/orientation example (level 1):", ex)
    g = check_q8_gauge(1); P(f"   random Q8 gauge transformation at level 1 (G = {g['gauge']}): classes equal {g['classes_equal']}/{g['n_inter_tile']}, signed labels equal {g['signed_labels_equal']}/{g['n_inter_tile']}; example: {g['example']}")
    su = check_su2_conjugation(); P("   SU(2) conjugation does not preserve Q8 classes:", su['U=(1+j)/sqrt2'])
    P("   generic SU(2) conjugation leaves Q8 entirely:", {k: v for k, v in su['generic_U'].items()})
    amb = {}
    for lvl in (1, 2):
        r = check_ambient_relabeling(lvl); amb[lvl] = r
        P(f"   level {lvl}: local-frame classes {r['local_frame_classes']} | ambient-axis classes (base cube 0) {r['ambient_axis_classes_base_cube0']} | "
          f"plaquettes whose AMBIENT axis depends on the base tile: {r['n_ambient_axis_depends_on_base_tile']}/{r['n_inter_tile']}"
          + (f" | spin-lift numeric check {r['spinlift_numeric_ok']}/{r['spinlift_numeric_checked']}" if r['spinlift_numeric_checked'] else ''))
        if r['example']: P("            example:", r['example'])
    P("   => the frequencies refer to Q8 classes = (trace, axis-in-local-frame); axis labels are meaningful only relative to the gauge-fixed local frames;")
    P("      the SU(2)-gauge-invariant (and base-point-independent in any gauge) content is the trace class {+1},{-1},{Tr=0}.")
    summary['gauge'] = g; summary['su2'] = {k: (v if k != 'generic_U' else {kk: (str(vv) if not isinstance(vv, (bool, float)) else vv) for kk, vv in v.items()}) for k, v in su.items()}
    summary['ambient'] = amb

    P(""); P("=" * 100); P("4. LIMITS AND NORMALIZATION FROM THE LEAN CERTIFICATE DATA ONLY")
    data = parse_lean_lists(); C = certificate_limits(data)
    P(f"   parsed: {C['nP']} panel types, {C['nQ']} plaquette types, N={C['N']}; S column sums panels {C['column_sums_panels']}, plaquettes {C['column_sums_plaquettes']}")
    P(f"   (8I - S) u = f solved over Fractions; residual verified exactly.  sum over plaquette types of u = {C['lim_N_over_8m']}; sum over panel types = {C['lim_panels_over_8m']}")
    P(f"   class limits u_c: { {k: str(v) for k, v in C['class_u'].items()} };  frequencies u_c/18: { {k: str(v) for k, v in C['freqs'].items()} }; Tr=0 total {C['trace0_freq']}")
    target = {'1': Fr(19, 36), '-1': Fr(13, 144), 'i': Fr(1, 9), 'j': Fr(23, 144), 'k': Fr(1, 9)}
    P(f"   equals (19/36, 13/144, 1/9, 23/144, 1/9): {C['freqs'] == target};  W8L/D == u: {C['W8_over_D_equals_u']};  v_m - 8^m u = S^(m-1)(f - 8u) for m=1..7: {C['residual_identity_ok']}")
    direct = read_direct_counts()
    P("   recursion v_{m+1} = S v_m + 8^m f, v_1 = f:")
    norm_ok = True; direct_ok = True
    for m in range(1, 8):
        r = C['recursion'][m]
        okN = r['plaquettes'] == r['plaquette_formula']; okP = r['panels'] == r['panel_formula']; norm_ok &= okN and okP
        dvals = {src: dd[m].get('inter_tile') for src, dd in direct.items() if m in dd and 'inter_tile' in dd[m]}
        pvals = {src: dd[m].get('panels') for src, dd in direct.items() if m in dd and dd[m].get('panels') is not None}
        cvals = {src: dd[m].get('classes') for src, dd in direct.items() if m in dd and dd[m].get('classes') is not None}
        dm = all(v == r['plaquettes'] for v in dvals.values()) and all(v == r['panels'] for v in pvals.values()) and all(v == r['classes'] for v in cvals.values())
        direct_ok &= dm
        P(f"     m={m}: plaquettes {r['plaquettes']} (18*8^m-24*4^m+6*2^m = {r['plaquette_formula']}: {okN}); panels {r['panels']} (12*(8^m-4^m) = {r['panel_formula']}: {okP}); classes {r['classes']}")
        if dvals or pvals: P(f"          direct values read from audit/results: plaquettes {dvals} panels {pvals} classes-match {bool(cvals) and all(v == r['classes'] for v in cvals.values())} -> all match recursion: {dm}")
    P(f"   normalization identities m=1..7: {norm_ok}; agreement with directly enumerated values (levels present in files): {direct_ok}")
    P("   NOTE: Phase 2 document states |E_k| = 48*12^(k-1) 'verified k<=3: 48, 576, 5376' -- 48*12^2 = 6912 != 5376; the correct closed form is 12*(8^k - 4^k).")
    summary['certificate'] = dict(nP=C['nP'], nQ=C['nQ'], lim_N_over_8m=str(C['lim_N_over_8m']), freqs={k: str(v) for k, v in C['freqs'].items()},
                                  trace0_freq=str(C['trace0_freq']), target_match=(C['freqs'] == target), W8_match=C['W8_over_D_equals_u'],
                                  normalization_ok=norm_ok, direct_match=direct_ok, residual_identity_ok=C['residual_identity_ok'],
                                  recursion={m: {k: (v if not isinstance(v, dict) else v) for k, v in C['recursion'][m].items()} for m in C['recursion']},
                                  direct_counts_read=direct)

    P(""); P("=" * 100); P("5. DECORATION DEPENDENCE (Thm 1.3 / Sec 1.4 counterexample) AND MIRROR INVARIANCE (Thm 2.4), RE-VERIFIED")
    dm = check_decoration_dependence_and_mirror()
    for k, v in dm.items(): P(f"   {k}: {v}")
    P("   => frequencies are invariants of the FR30-decorated Clifford connection modulo Q8 gauge (parity-invariant), NOT of the point-set tiling.")
    summary['decoration'] = dm

    P(""); P(f"total time {time.time() - t0:.1f}s")
    open(out_txt, 'w').write('\n'.join(lines) + '\n')
    json.dump(summary, open(out_json, 'w'), indent=1, default=str)
    print("written:", out_txt, out_json)


if __name__ == '__main__':
    main()
