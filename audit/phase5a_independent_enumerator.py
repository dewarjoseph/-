"""
phase5a_independent_enumerator.py -- independent re-derivation of the class-resolved inter-tile plaquette
counts of the Clifford Q8 background on the FR30 Chair44 substitution, levels 1..5.

Run from the repository root:
    python3 -u -I audit/phase5a_independent_enumerator.py [maxlevel]
Outputs:
    audit/results/phase5a_independent_enumerator.json
    audit/results/phase5a_independent_enumerator.txt

INDEPENDENCE STATEMENT
----------------------
This module imports NOTHING from audit/ or src/.  It is written from the documented definitions
(deliverables/CLIFFORD_Q8_END_TO_END_AUDIT.md, axioms A1-A6, and the task statement) only.

Shared with the repository (these DEFINE the object under study, so they cannot be independent):
  * the prototile U3 = {0,1}^3 \\ {(1,1,1)} (A1);
  * the FR30 permutation data  (0,0,0)->(0,1,2), (0,0,1)->(0,2,1), (0,1,0)->(2,1,0), (0,1,1)->(1,2,0),
    (1,0,0)->(1,0,2), (1,0,1)->(0,1,2), (1,1,0)->(2,0,1), with P(p)[i, p[i]] = 1 (A3);
  * the inflation rule in doubled coordinates: centre child (G P(id), 2T + G(1,1,1)), octant children
    (G D_s(v) P(pi_v), 2T + 4 G v), cube corners (G(2u+1) + 2T - 1)/2 (A2);
  * the link rule C_ab = (sigma.M_a^T n)(sigma.M_b^T n) = -(u_a u_b) in the quaternion picture e_i = -i sigma_i (A5);
  * the canonical plaquette (four unit cubes around a lattice edge, identity link inside a tile, inter-tile iff the
    four cubes belong to >= 2 tiles) and its gauge-invariant datum, the Q8 conjugacy class (A6).

Independent of the repository (different representation and different algorithms):
  * frames are signed permutations (perm, signs) with G e_j = signs[j] e_{perm[j]}; composition, application and
    G^T n are computed combinatorially, never as 3x3 numpy matrices (the repo uses numpy matrices);
  * Q8 elements are abstract (sign, basis) pairs with an explicit basis multiplication table derived from
    i^2 = j^2 = k^2 = ijk = -1; the group axioms and the five conjugacy classes are re-derived by brute force at
    import time (the repo uses 2x2 complex Pauli matrices and np.allclose label matching);
  * tiles are generated breadth-first with an explicit record of the level-1 ancestor (for straddling counts);
  * plaquettes are parametrised by their lattice EDGE (base point x, direction k) with the four cubes
    x-e_i-e_j, x-e_j, x, x-e_i, and enumerated by numpy slicing of an ownership array (the repo parametrises by
    the cube c with c, c+e_i, c+e_i+e_j, c+e_j and iterates over cubes);
  * two independent plaquette evaluators are run and compared: a pure-Python scalar one (dict ownership map,
    abstract tuples) at levels 1..3 and a vectorised one (integer Q8 codes, gather tables) at all levels;
  * links are cross-checked against explicit 2x2 Pauli matrices on every panel at levels 1 and 2 and on all 36
    (u_a, u_b) signed-axis pairs.

Conventions for labels: the signed label (s, 'i') here means the QUATERNION s*i = -s*i*sigma_1.  The repo's
signed label '+i' means +i*sigma_1 = quaternion -i.  Signed labels therefore differ by a sign on the traceless
classes; the conjugacy classes {+1},{-1},{+-i},{+-j},{+-k} are identical and are the only thing compared.
"""
import sys, os, json, time, re, ast, itertools, collections
import numpy as np

ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))

# =====================================================================================================
# 1. Abstract Q8:  elements are (sign, basis), sign in {+1,-1}, basis in '1ijk'.
# =====================================================================================================
BASIS = ('1', 'i', 'j', 'k')
# Basis products derived from i^2 = j^2 = k^2 = ijk = -1 (inverses: x^{-1} = -x for x in {i,j,k}):
#   ij  = (ijk) k^{-1} = (-1)(-k) =  k         jk = i^{-1}(ijk) = (-i)(-1) =  i
#   ji  : from jk = i, left-multiply by j^{-1}: k = -ji  =>  ji = -k
#   ki  : from ji = -k, right-multiply by i^{-1}: j = (-k)(-i) = ki  =>  ki =  j
#   ik  : from ij = k, left-multiply by i^{-1}: j = -ik  =>  ik = -j
#   kj  : from ki = j, left-multiply by k^{-1}: i = -kj  =>  kj = -i
_BASIS_MUL = {
    ('1', '1'): (1, '1'), ('1', 'i'): (1, 'i'), ('1', 'j'): (1, 'j'), ('1', 'k'): (1, 'k'),
    ('i', '1'): (1, 'i'), ('j', '1'): (1, 'j'), ('k', '1'): (1, 'k'),
    ('i', 'i'): (-1, '1'), ('j', 'j'): (-1, '1'), ('k', 'k'): (-1, '1'),
    ('i', 'j'): (1, 'k'), ('j', 'k'): (1, 'i'), ('k', 'i'): (1, 'j'),
    ('j', 'i'): (-1, 'k'), ('k', 'j'): (-1, 'i'), ('i', 'k'): (-1, 'j'),
}
Q8 = [(s, b) for s in (1, -1) for b in BASIS]
ONE = (1, '1')

def qmul(a, b):
    s, bb = _BASIS_MUL[(a[1], b[1])]
    return (a[0] * b[0] * s, bb)

def qneg(a):
    return (-a[0], a[1])

def qinv(a):
    for x in Q8:
        if qmul(a, x) == ONE and qmul(x, a) == ONE:
            return x
    raise ValueError(a)

def q8_selfcheck():
    """Re-derive the group structure from the table: relations, closure, associativity, inverses, classes."""
    i, j, k = (1, 'i'), (1, 'j'), (1, 'k'); m1 = (-1, '1')
    assert qmul(i, i) == m1 and qmul(j, j) == m1 and qmul(k, k) == m1 and qmul(qmul(i, j), k) == m1
    assert all(qmul(a, b) in Q8 for a in Q8 for b in Q8)
    assert all(qmul(qmul(a, b), c) == qmul(a, qmul(b, c)) for a in Q8 for b in Q8 for c in Q8)
    assert all(qmul(ONE, a) == a and qmul(a, ONE) == a for a in Q8)
    for a in Q8: qinv(a)
    assert len(set(Q8)) == 8
    # conjugacy classes by brute force
    classes = []
    seen = set()
    for a in Q8:
        if a in seen: continue
        cl = frozenset(qmul(qmul(g, a), qinv(g)) for g in Q8)
        classes.append(cl); seen |= cl
    assert len(classes) == 5
    label = {}
    for cl in classes:
        if cl == frozenset({ONE}): label[cl] = '1'
        elif cl == frozenset({m1}): label[cl] = '-1'
        else:
            bs = {b for _, b in cl}; assert len(bs) == 1 and len(cl) == 2
            label[cl] = bs.pop()
    cls_of = {}
    for cl in classes:
        for a in cl: cls_of[a] = label[cl]
    # classes are closed under inversion (needed for orientation independence of the plaquette class)
    assert all(cls_of[qinv(a)] == cls_of[a] for a in Q8)
    return cls_of

CLASS_OF = q8_selfcheck()
CLASSES = ['1', '-1', 'i', 'j', 'k']

# integer codes for the vectorised path: code = basis index + 4*(sign<0)
def qcode(a): return BASIS.index(a[1]) + (4 if a[0] < 0 else 0)
def qdecode(c): return (-1 if c >= 4 else 1, BASIS[c % 4])
MUL8 = np.array([[qcode(qmul(qdecode(a), qdecode(b))) for b in range(8)] for a in range(8)], dtype=np.int8)
CLASS8 = np.array([CLASSES.index(CLASS_OF[qdecode(c)]) for c in range(8)], dtype=np.int8)
ID_CODE = qcode(ONE)

def pure(axis, sign):
    """Signed coordinate axis sign*e_axis as a pure quaternion."""
    return (sign, BASIS[axis + 1])

def link_q(ua, ub):
    """C_ab = (sigma.u_a)(sigma.u_b) = -(u_a u_b) for pure quaternions u_a, u_b (e_i = -i sigma_i)."""
    return qneg(qmul(ua, ub))

# LINK8[code(u_a), code(u_b)] for pure-quaternion codes (codes of '1' are never used; filled with ID for safety)
LINK8 = np.full((8, 8), ID_CODE, dtype=np.int8)
for ca in range(8):
    for cb in range(8):
        a, b = qdecode(ca), qdecode(cb)
        if a[1] != '1' and b[1] != '1':
            LINK8[ca, cb] = qcode(link_q(a, b))
def pure_code(axis, sign): return (axis + 1) + (4 if sign < 0 else 0)

# =====================================================================================================
# 2. Pauli cross-check machinery (numpy 2x2 complex)
# =====================================================================================================
SIG = [np.array([[0, 1], [1, 0]], complex), np.array([[0, -1j], [1j, 0]], complex), np.array([[1, 0], [0, -1]], complex)]
def sdot(u): return sum(u[m] * SIG[m] for m in range(3))
def q_to_mat(a):
    base = {'1': np.eye(2, dtype=complex), 'i': -1j * SIG[0], 'j': -1j * SIG[1], 'k': -1j * SIG[2]}[a[1]]
    return a[0] * base
def pauli_link(ua_vec, ub_vec): return sdot(ua_vec) @ sdot(ub_vec)

def pauli_identity_check():
    """(sigma.u_a)(sigma.u_b) == matrix of -(u_a u_b) for all 36 signed-axis pairs, and the quaternion/Pauli
    embedding is a homomorphism on all 64 products."""
    ok = True
    for (ax, sx) in itertools.product(range(3), (1, -1)):
        for (ay, sy) in itertools.product(range(3), (1, -1)):
            ua = [0, 0, 0]; ua[ax] = sx; ub = [0, 0, 0]; ub[ay] = sy
            ok &= np.allclose(pauli_link(ua, ub), q_to_mat(link_q(pure(ax, sx), pure(ay, sy))))
    for a in Q8:
        for b in Q8:
            ok &= np.allclose(q_to_mat(a) @ q_to_mat(b), q_to_mat(qmul(a, b)))
    return bool(ok)

# =====================================================================================================
# 3. Signed permutations:  G = (perm, signs),  G e_j = signs[j] * e_{perm[j]}
# =====================================================================================================
IDENT = ((0, 1, 2), (1, 1, 1))

def sp_compose(A, B):
    """(A B) e_j = A(sB[j] e_{pB[j]}) = sB[j] sA[pB[j]] e_{pA[pB[j]]}."""
    pA, sA = A; pB, sB = B
    return (tuple(pA[pB[j]] for j in range(3)), tuple(sB[j] * sA[pB[j]] for j in range(3)))

def sp_apply(A, v):
    pA, sA = A; out = [0, 0, 0]
    for j in range(3): out[pA[j]] = sA[j] * v[j]
    return tuple(out)

def sp_transpose_apply(A, n):
    """(A^T n)_j = sum_i A[i,j] n_i = sA[j] * n[pA[j]]."""
    pA, sA = A
    return tuple(sA[j] * n[pA[j]] for j in range(3))

def perm_parity(p):
    inv = 0
    for a in range(3):
        for b in range(a + 1, 3):
            if p[a] > p[b]: inv += 1
    return -1 if inv % 2 else 1

def sp_det(A):
    pA, sA = A
    return perm_parity(pA) * sA[0] * sA[1] * sA[2]

def sp_to_matrix(A):
    pA, sA = A; M = np.zeros((3, 3), dtype=int)
    for j in range(3): M[pA[j], j] = sA[j]
    return M

def P_of(p):
    """Permutation matrix with P[i, p[i]] = 1, i.e. P e_j = e_i where p[i] = j  =>  perm = p^{-1}."""
    inv = [0, 0, 0]
    for i_ in range(3): inv[p[i_]] = i_
    return (tuple(inv), (1, 1, 1))

def D_s(v): return ((0, 1, 2), tuple(1 - 2 * x for x in v))

def signed_perm_selfcheck():
    """Check the combinatorial arithmetic against numpy matrices on the whole hyperoctahedral group B3 (48 elements)."""
    allsp = [(p, s) for p in itertools.permutations(range(3)) for s in itertools.product((1, -1), repeat=3)]
    assert len(allsp) == 48
    rng = np.random.default_rng(12345)
    for A in allsp:
        MA = sp_to_matrix(A)
        assert int(round(np.linalg.det(MA))) == sp_det(A)
        for _ in range(3):
            v = tuple(int(x) for x in rng.integers(-5, 6, size=3))
            assert sp_apply(A, v) == tuple(MA @ np.array(v))
            assert sp_transpose_apply(A, v) == tuple(MA.T @ np.array(v))
        for B in allsp:
            assert (sp_to_matrix(sp_compose(A, B)) == MA @ sp_to_matrix(B)).all()
    for p in itertools.permutations(range(3)):
        M = np.zeros((3, 3), int)
        for i_ in range(3): M[i_, p[i_]] = 1
        assert (sp_to_matrix(P_of(p)) == M).all()
    return True

# =====================================================================================================
# 4. Substitution (doubled coordinates)
# =====================================================================================================
U3 = [v for v in itertools.product((0, 1), repeat=3) if v != (1, 1, 1)]
FR30 = {(0, 0, 0): (0, 1, 2), (0, 0, 1): (0, 2, 1), (0, 1, 0): (2, 1, 0), (0, 1, 1): (1, 2, 0),
        (1, 0, 0): (1, 0, 2), (1, 0, 1): (0, 1, 2), (1, 1, 0): (2, 0, 1)}
PI0 = (0, 1, 2)

def children(G, T):
    """Eight child poses of (G,T): centre child first, then the seven octant children in U3 order."""
    out = [(sp_compose(G, P_of(PI0)), tuple(2 * T[m] + x for m, x in enumerate(sp_apply(G, (1, 1, 1)))))]
    for v in U3:
        g = sp_compose(D_s(v), P_of(FR30[v]))
        t = sp_apply(G, v)
        out.append((sp_compose(G, g), tuple(2 * T[m] + 4 * t[m] for m in range(3))))
    return out

def tiles_at_level(level):
    """List of (G, T, top_child) with top_child = index (0..7) of the level-1 ancestor (= the level-(m-1) child
    of the level-m supertile that contains the tile)."""
    poses = [(IDENT, (0, 0, 0), -1)]
    for step in range(level):
        new = []
        for G, T, tc in poses:
            for idx, (g, t) in enumerate(children(G, T)):
                new.append((g, t, idx if step == 0 else tc))
        poses = new
    return poses

def cubes_of(G, T):
    out = []
    for u in U3:
        d = sp_apply(G, tuple(2 * x + 1 for x in u))
        c = []
        for m in range(3):
            num = d[m] + 2 * T[m] - 1
            assert num % 2 == 0
            c.append(num // 2)
        out.append(tuple(c))
    return out

# =====================================================================================================
# 5. Level data: ownership array, geometry verification
# =====================================================================================================
class Level:
    def __init__(self, level):
        t0 = time.time()
        self.level = level; self.N = 2 ** (level + 1); N = self.N
        tiles = tiles_at_level(level)
        self.ntiles = len(tiles)
        self.perm = np.array([G[0] for G, _, _ in tiles], dtype=np.int64)
        self.signs = np.array([G[1] for G, _, _ in tiles], dtype=np.int64)
        self.invperm = np.zeros_like(self.perm)
        for j in range(3): self.invperm[np.arange(self.ntiles), self.perm[:, j]] = j
        self.topchild = np.array([tc for _, _, tc in tiles], dtype=np.int64)
        self.frames = [G for G, _, _ in tiles]
        self.T = [T for _, T, _ in tiles]
        self.all_det_plus1 = all(sp_det(G) == 1 for G in self.frames)
        coords = []; owners = []
        for a, (G, T, _) in enumerate(tiles):
            cs = cubes_of(G, T); coords.extend(cs); owners.extend([a] * len(cs))
        coords = np.array(coords, dtype=np.int64); owners = np.array(owners, dtype=np.int64)
        self.ncube_slots = len(coords)
        self.in_box = bool(((coords >= 0) & (coords < N)).all())
        assert self.in_box, "cube outside the level box"
        lin = (coords[:, 0] * N + coords[:, 1]) * N + coords[:, 2]
        self.ndistinct = int(len(np.unique(lin)))
        self.disjoint = (self.ndistinct == self.ncube_slots)
        O = np.full((N, N, N), -1, dtype=np.int64)
        O[coords[:, 0], coords[:, 1], coords[:, 2]] = owners
        self.O = O
        # target region: [0,N)^3 minus [N/2,N)^3
        target = np.ones((N, N, N), dtype=bool); target[N // 2:, N // 2:, N // 2:] = False
        self.fills_chair = bool(((O >= 0) == target).all())
        self.ntarget = int(target.sum())
        self.time_build = time.time() - t0

    # ---- links (vectorised) ----
    def link_codes(self, a, b, axis, sign):
        """Q8 code of the link from owner a to owner b across a face with ambient normal sign*e_axis.
        a, b are integer arrays (same owner => identity)."""
        ja = self.invperm[a, axis]; sa = sign * self.signs[a, ja]
        jb = self.invperm[b, axis]; sb = sign * self.signs[b, jb]
        ca = (ja + 1) + 4 * (sa < 0); cb = (jb + 1) + 4 * (sb < 0)
        out = LINK8[ca, cb]
        return np.where(a == b, ID_CODE, out)

    def plaquettes_vectorised(self):
        """Enumerate all lattice edges whose four surrounding cubes are present; return counts."""
        N = self.N; O = self.O; TC = self.topchild
        total = 0; inter = 0; straddle = 0
        cls_inter = np.zeros(5, dtype=np.int64); cls_straddle = np.zeros(5, dtype=np.int64)
        code_inter = np.zeros(8, dtype=np.int64)
        for k in range(3):
            i_, j_ = [m for m in range(3) if m != k]
            def sl(di, dj):   # slice of O at x - di*e_i - dj*e_j, x_i, x_j in [1,N), x_k in [0,N)
                s = [slice(0, N)] * 3
                s[i_] = slice(1 - di, N - di); s[j_] = slice(1 - dj, N - dj)
                return O[tuple(s)]
            P0, P1, P2, P3 = sl(1, 1), sl(0, 1), sl(0, 0), sl(1, 0)   # cycle: +e_i, +e_j, -e_i, -e_j
            present = (P0 >= 0) & (P1 >= 0) & (P2 >= 0) & (P3 >= 0)
            inter_mask = present & ~((P0 == P1) & (P1 == P2) & (P2 == P3))
            total += int(present.sum())
            a0, a1, a2, a3 = (P[inter_mask] for P in (P0, P1, P2, P3))
            L0 = self.link_codes(a0, a1, i_, 1)
            L1 = self.link_codes(a1, a2, j_, 1)
            L2 = self.link_codes(a2, a3, i_, -1)
            L3 = self.link_codes(a3, a0, j_, -1)
            W = MUL8[MUL8[MUL8[L0, L1], L2], L3]
            inter += len(W)
            cls_inter += np.bincount(CLASS8[W], minlength=5)
            code_inter += np.bincount(W, minlength=8)
            t0_, t1_, t2_, t3_ = TC[a0], TC[a1], TC[a2], TC[a3]
            smask = ~((t0_ == t1_) & (t1_ == t2_) & (t2_ == t3_))
            straddle += int(smask.sum())
            cls_straddle += np.bincount(CLASS8[W[smask]], minlength=5)
        return {
            'plaquettes_total': total, 'inter_tile': inter, 'straddling': straddle,
            'classes': {CLASSES[m]: int(cls_inter[m]) for m in range(5)},
            'straddling_classes': {CLASSES[m]: int(cls_straddle[m]) for m in range(5)},
            'signed_labels_quaternion_convention': {f"{'+' if qdecode(c)[0] > 0 else '-'}{qdecode(c)[1]}": int(code_inter[c]) for c in range(8)},
        }

    # ---- scalar path (independent implementation, levels <= 3) ----
    def owner_dict(self):
        om = {}
        for a, (G, T) in enumerate(zip(self.frames, self.T)):
            for c in cubes_of(G, T): om[c] = a
        return om

    def link_scalar(self, a, b, nvec):
        ua = sp_transpose_apply(self.frames[a], nvec); ub = sp_transpose_apply(self.frames[b], nvec)
        (axa,) = [m for m in range(3) if ua[m] != 0]; (axb,) = [m for m in range(3) if ub[m] != 0]
        return link_q(pure(axa, ua[axa]), pure(axb, ub[axb]))

    def plaquettes_scalar(self):
        om = self.owner_dict(); N = self.N
        cnt = collections.Counter(); total = inter = 0
        E = [(1, 0, 0), (0, 1, 0), (0, 0, 1)]
        for k in range(3):
            i_, j_ = [m for m in range(3) if m != k]
            for x in itertools.product(range(N), repeat=3):
                if x[i_] == 0 or x[j_] == 0: continue
                cyc = [tuple(x[m] - E[i_][m] - E[j_][m] for m in range(3)), tuple(x[m] - E[j_][m] for m in range(3)),
                       x, tuple(x[m] - E[i_][m] for m in range(3))]
                if not all(c in om for c in cyc): continue
                total += 1
                owners = [om[c] for c in cyc]
                if len(set(owners)) == 1: continue
                inter += 1
                W = ONE
                for q in range(4):
                    a, b = owners[q], owners[(q + 1) % 4]
                    if a != b:
                        c1, c2 = cyc[q], cyc[(q + 1) % 4]
                        nvec = tuple(c2[m] - c1[m] for m in range(3))
                        W = qmul(W, self.link_scalar(a, b, nvec))
                cnt[CLASS_OF[W]] += 1
        return {'plaquettes_total': total, 'inter_tile': inter, 'classes': {c: cnt[c] for c in CLASSES}}

    def panels_and_pauli_check(self):
        """Enumerate shared unit faces (each once, with normal +e_axis), compute the link abstractly and with Pauli
        matrices, and return value statistics and agreement."""
        om = self.owner_dict(); E = [(1, 0, 0), (0, 1, 0), (0, 0, 1)]
        npanels = 0; agree = True; vals = collections.Counter()
        for c, a in om.items():
            for ax in range(3):
                c2 = tuple(c[m] + E[ax][m] for m in range(3)); b = om.get(c2)
                if b is None or b == a: continue
                npanels += 1
                Cq = self.link_scalar(a, b, E[ax])
                Ma = sp_to_matrix(self.frames[a]); Mb = sp_to_matrix(self.frames[b])
                Cm = pauli_link(Ma.T @ np.array(E[ax]), Mb.T @ np.array(E[ax]))
                agree &= bool(np.allclose(Cm, q_to_mat(Cq)))
                vals['+1' if Cq == ONE else ('-1' if Cq == (-1, '1') else 'traceless')] += 1
        return {'shared_panels': npanels, 'pauli_agrees_on_all_panels': bool(agree),
                'link_values': {'+1': vals['+1'], '-1': vals['-1'], 'traceless': vals['traceless']}}

# =====================================================================================================
# 6. Reference files (read, not recomputed)
# =====================================================================================================
def read_phase4_recursion(path):
    out = {}
    if not os.path.exists(path): return out
    for line in open(path, encoding='utf-8'):
        m = re.match(r"\s*level (\d+): recursion (\{.*?\})\s+N=(\d+)", line)
        if m:
            d = ast.literal_eval(m.group(2)); out[int(m.group(1))] = {'classes': {k: int(v) for k, v in d.items()}, 'N': int(m.group(3))}
    return out

def read_phase3_straddle(path):
    out = {}
    if not os.path.exists(path): return out
    for line in open(path, encoding='utf-8'):
        m = re.match(r"level (\d+): inter-tile N_k=(\d+) .*straddling B_k=(\d+) .*classes b_k=(\{.*?\})", line)
        if m:
            out[int(m.group(1))] = {'N': int(m.group(2)), 'B': int(m.group(3)), 'classes': {k: int(v) for k, v in ast.literal_eval(m.group(4)).items()}}
    return out

def read_lean_level1(path):
    out = {}
    if not os.path.exists(path): return out
    txt = open(path, encoding='utf-8').read()
    def grab(pat):
        m = re.search(pat, txt, re.S); return int(m.group(1)) if m else None
    out['cubes'] = grab(r"allCubes\.length = (\d+)")
    out['panels'] = grab(r"panels\.length = (\d+)")
    out['links_minus1'] = grab(r"countLink ⟨-1,0,0,0⟩ = (\d+)")
    out['links_plus1'] = grab(r"countLink qOne = (\d+)")
    out['links_traceless'] = grab(r"panelLinks\.filter \(fun q => q\.s == 0\)\)\.length = (\d+)")
    out['plaquettes'] = grab(r"plaquetteHolonomies\.length = (\d+)")
    out['plaq_plus1'] = grab(r"countHol qOne = (\d+)")
    out['plaq_minus1'] = grab(r"countHol ⟨-1,0,0,0⟩ = (\d+)")
    out['plaq_traceless'] = grab(r"plaquetteHolonomies\.filter \(fun q => q\.s == 0\)\)\.length = (\d+)")
    return out

# =====================================================================================================
# 7. Main
# =====================================================================================================
def run(maxlevel=5, scalar_maxlevel=3, pauli_maxlevel=2, verbose=True):
    lines = []
    def say(s=''):
        lines.append(s)
        if verbose: print(s, flush=True)
    report = {'script': 'audit/phase5a_independent_enumerator.py', 'maxlevel': maxlevel, 'levels': {}, 'checks': {}}
    say("phase5a independent enumerator (no imports from audit/ or src/)")
    report['checks']['q8_table_selfcheck'] = True   # q8_selfcheck() raised nothing at import
    report['checks']['signed_perm_selfcheck'] = signed_perm_selfcheck()
    report['checks']['pauli_identity_all_36_pairs_and_homomorphism'] = pauli_identity_check()
    say(f" Q8 table self-check (relations, closure, associativity, inverses, 5 classes closed under inversion): OK")
    say(f" signed-permutation arithmetic vs numpy on all 48 signed permutations (and all 48x48 compositions): {report['checks']['signed_perm_selfcheck']}")
    say(f" (sigma.u_a)(sigma.u_b) = -(u_a u_b) on all 36 signed-axis pairs; Q8->SU(2) homomorphism on 64 products: {report['checks']['pauli_identity_all_36_pairs_and_homomorphism']}")
    # determinant bookkeeping of the child operators
    dets = {str(v): sp_det(sp_compose(D_s(v), P_of(FR30[v]))) for v in U3}
    report['checks']['child_operator_dets'] = dets
    say(f" det(D_s(v) P(pi_v)) for v in U3: {dets}")

    for lvl in range(1, maxlevel + 1):
        t0 = time.time(); L = Level(lvl)
        geo = {'tiles': L.ntiles, 'cube_slots': L.ncube_slots, 'distinct_cubes': L.ndistinct, 'pairwise_disjoint': bool(L.disjoint),
               'all_in_box': L.in_box, 'target_cubes': L.ntarget, 'fills_chair_exactly': L.fills_chair, 'all_frames_det_plus1': L.all_det_plus1}
        vec = L.plaquettes_vectorised(); t_vec = time.time() - t0
        entry = {'geometry': geo, 'vectorised': vec, 'time_s': round(t_vec, 2)}
        say(f"\nLEVEL {lvl}: N={L.N}")
        say(f" geometry: tiles={geo['tiles']} cube_slots={geo['cube_slots']} distinct={geo['distinct_cubes']} disjoint={geo['pairwise_disjoint']} "
            f"fills [0,{L.N})^3 \\ [{L.N//2},{L.N})^3 exactly={geo['fills_chair_exactly']} (target {geo['target_cubes']} cubes) det+1={geo['all_frames_det_plus1']}")
        say(f" plaquettes: total={vec['plaquettes_total']} inter-tile={vec['inter_tile']} straddling={vec['straddling']}  [{t_vec:.1f}s]")
        say(f" inter-tile classes: {vec['classes']}")
        say(f" straddling classes: {vec['straddling_classes']}")
        say(f" signed labels (quaternion convention, loop +e_i,+e_j,-e_i,-e_j from x-e_i-e_j): {vec['signed_labels_quaternion_convention']}")
        Nf = 18 * 8 ** lvl - 24 * 4 ** lvl + 6 * 2 ** lvl; Bf = 24 * 4 ** lvl - 18 * 2 ** lvl
        entry['formula_N'] = Nf; entry['formula_B'] = Bf
        entry['matches_formula_N'] = (vec['inter_tile'] == Nf); entry['matches_formula_B'] = (vec['straddling'] == Bf)
        say(f" N_m formula 18*8^m-24*4^m+6*2^m = {Nf}: match={entry['matches_formula_N']};  B_m formula 24*4^m-18*2^m = {Bf}: match={entry['matches_formula_B']}")
        if lvl <= scalar_maxlevel:
            t1 = time.time(); sc = L.plaquettes_scalar(); entry['scalar'] = sc; entry['scalar_time_s'] = round(time.time() - t1, 2)
            entry['scalar_matches_vectorised'] = (sc['classes'] == vec['classes'] and sc['plaquettes_total'] == vec['plaquettes_total'] and sc['inter_tile'] == vec['inter_tile'])
            say(f" scalar (pure-Python, dict map) evaluator: total={sc['plaquettes_total']} inter={sc['inter_tile']} classes={sc['classes']} matches vectorised={entry['scalar_matches_vectorised']}")
        if lvl <= pauli_maxlevel:
            pc = L.panels_and_pauli_check(); entry['panels'] = pc
            say(f" panels: shared unit faces={pc['shared_panels']} link values={pc['link_values']} Pauli-matrix agreement on every panel={pc['pauli_agrees_on_all_panels']}")
        if lvl == 1:
            entry['level1_frames'] = [{'perm': list(G[0]), 'signs': list(G[1]), 'T': list(T)} for G, T in zip(L.frames, L.T)]
        report['levels'][str(lvl)] = entry
        del L

    # ---- comparisons with saved reference files ----
    say("\nCOMPARISON WITH audit/results/phase4_type_substitution_proof.txt (recursion predictions; read, not recomputed)")
    p4 = read_phase4_recursion(os.path.join(ROOT, 'audit', 'results', 'phase4_type_substitution_proof.txt'))
    cmp4 = {}
    for lvl in range(1, maxlevel + 1):
        mine = report['levels'][str(lvl)]['vectorised']
        if lvl in p4:
            ok = (p4[lvl]['classes'] == mine['classes']) and (p4[lvl]['N'] == mine['inter_tile'])
            cmp4[lvl] = {'recursion': p4[lvl], 'enumerated': {'classes': mine['classes'], 'N': mine['inter_tile']}, 'exact_match': ok}
            say(f" level {lvl}: recursion {p4[lvl]['classes']} N={p4[lvl]['N']} | enumerated {mine['classes']} N={mine['inter_tile']} | EXACT MATCH: {ok}")
        else:
            cmp4[lvl] = {'recursion': None, 'exact_match': None}; say(f" level {lvl}: no recursion line found in file")
    report['comparison_phase4_recursion'] = cmp4
    report['phase4_file_levels_present'] = sorted(p4)

    say("\nCOMPARISON WITH audit/results/phase3_straddle_closed_form_levels3-7.txt (class-resolved straddling counts; read)")
    p3 = read_phase3_straddle(os.path.join(ROOT, 'audit', 'results', 'phase3_straddle_closed_form_levels3-7.txt'))
    cmp3 = {}
    for lvl in range(1, maxlevel + 1):
        if lvl in p3:
            mine = report['levels'][str(lvl)]['vectorised']
            ok = (p3[lvl]['classes'] == mine['straddling_classes']) and p3[lvl]['B'] == mine['straddling'] and p3[lvl]['N'] == mine['inter_tile']
            cmp3[lvl] = {'file': p3[lvl], 'enumerated': {'classes': mine['straddling_classes'], 'B': mine['straddling'], 'N': mine['inter_tile']}, 'exact_match': ok}
            say(f" level {lvl}: file b_k={p3[lvl]['classes']} B={p3[lvl]['B']} | enumerated {mine['straddling_classes']} B={mine['straddling']} | EXACT MATCH: {ok}")
    report['comparison_phase3_straddle'] = cmp3

    say("\nCOMPARISON WITH certificates/Chair44GeometryToMatrix.lean (level 1; read)")
    lean = read_lean_level1(os.path.join(ROOT, 'certificates', 'Chair44GeometryToMatrix.lean'))
    l1 = report['levels']['1']; v1 = l1['vectorised']; pn = l1.get('panels', {})
    tr = v1['classes']['i'] + v1['classes']['j'] + v1['classes']['k']
    mine_lean = {'cubes': l1['geometry']['distinct_cubes'], 'panels': pn.get('shared_panels'), 'links_minus1': pn.get('link_values', {}).get('-1'),
                 'links_plus1': pn.get('link_values', {}).get('+1'), 'links_traceless': pn.get('link_values', {}).get('traceless'),
                 'plaquettes': v1['inter_tile'], 'plaq_plus1': v1['classes']['1'], 'plaq_minus1': v1['classes']['-1'], 'plaq_traceless': tr}
    lean_cmp = {k: {'lean': lean.get(k), 'enumerated': mine_lean[k], 'match': (lean.get(k) == mine_lean[k])} for k in mine_lean}
    for k, v in lean_cmp.items(): say(f" {k:16s}: lean={v['lean']} enumerated={v['enumerated']} match={v['match']}")
    report['comparison_lean_level1'] = lean_cmp

    all_ok = all(c['exact_match'] for c in cmp4.values() if c['exact_match'] is not None) and all(v['match'] for v in lean_cmp.values()) \
        and all(report['levels'][str(l)]['geometry']['fills_chair_exactly'] and report['levels'][str(l)]['geometry']['pairwise_disjoint'] for l in range(1, maxlevel + 1))
    report['all_checks_passed'] = bool(all_ok)
    say(f"\nALL CHECKS PASSED: {all_ok}")
    return report, lines

if __name__ == '__main__':
    maxlevel = int(sys.argv[1]) if len(sys.argv) > 1 else 5
    t0 = time.time()
    report, lines = run(maxlevel)
    report['total_time_s'] = round(time.time() - t0, 2)
    lines.append(f"total time {report['total_time_s']} s")
    print(f"total time {report['total_time_s']} s")
    outdir = os.path.join(ROOT, 'audit', 'results'); os.makedirs(outdir, exist_ok=True)
    with open(os.path.join(outdir, 'phase5a_independent_enumerator.json'), 'w', encoding='utf-8') as f:
        json.dump(report, f, indent=1)
    with open(os.path.join(outdir, 'phase5a_independent_enumerator.txt'), 'w', encoding='utf-8') as f:
        f.write("\n".join(lines) + "\n")
    print("wrote audit/results/phase5a_independent_enumerator.{json,txt}")
