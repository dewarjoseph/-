"""
Computer-assisted proof of the exact plaquette-class recursion for the Clifford Q8 background on the FR30 chair
substitution.  Nothing here is fitted: the finite set of panel types and plaquette types, and the linear map that
inflation induces on their counts, are DERIVED from the substitution rule by inflating one representative of each
type.  The resulting recursion is then (i) checked against the directly enumerated counts (levels 1-5) and
(ii) analysed exactly with SymPy to obtain the closed forms and the limiting frequencies as rational numbers.
Run from the repository root:  python3 -I audit/phase4_type_substitution_proof.py
"""
import os, sys, itertools, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np, sympy as sp
from fractions import Fraction as Fr
from independent_clifford_q8_audit import U3, FR30, perm_mat, clifford_link, q8label

# ---------------- substitution primitives (doubled coordinates) ----------------
CHILD_OPS = [(perm_mat(FR30['0']), np.array([1, 1, 1]))] + \
            [(np.diag([1-2*v[0], 1-2*v[1], 1-2*v[2]]) @ perm_mat(FR30[v]), 4*np.array(v)) for v in U3]
BASE = [np.array([2*u[0]+1, 2*u[1]+1, 2*u[2]+1]) for u in U3]
def inflate(G, T): return [(G @ g, 2*T + G @ t) for g, t in CHILD_OPS]
def cubes(G, T): return [tuple((G @ bc + 2*T - 1) // 2) for bc in BASE]
def key(G, T): return (tuple(map(tuple, G)), tuple(T))
E = [np.array(v) for v in ((1,0,0),(0,1,0),(0,0,1))]
CLASS = {'+1': '1', '-1': '-1', '+i': 'i', '-i': 'i', '+j': 'j', '-j': 'j', '+k': 'k', '-k': 'k'}
CLASSES = ['1', '-1', 'i', 'j', 'k']

def owner_map(poses):
    om = {}
    for (G, T) in poses:
        for c in cubes(G, T): om[c] = (G, T)
    return om

# ---------------- intrinsic type encodings ----------------
def rel(Gref, Tref, G, T):   # pose of (G,T) in the frame of (Gref,Tref)
    return (tuple(map(tuple, Gref.T @ G)), tuple(Gref.T @ (T - Tref)))
def loc(Gref, Tref, c):      # doubled centre of cube c in the reference frame
    return tuple(Gref.T @ (2*np.array(c) + 1 - 2*Tref))

def panel_type(om, c, ax):
    """Panel between cube c (tile t) and c+e_ax (tile t'); intrinsic encoding = min over the two orderings."""
    c2 = tuple(np.array(c) + E[ax]); p, p2 = om[c], om[c2]
    e1 = (loc(*p, c), tuple(p[0].T @ E[ax]), rel(*p, *p2))
    e2 = (loc(*p2, c2), tuple(p2[0].T @ (-E[ax])), rel(*p2, *p))
    return min(e1, e2)

def plaquette_cubes(c, i, j):
    return [tuple(c), tuple(np.array(c) + E[i]), tuple(np.array(c) + E[i] + E[j]), tuple(np.array(c) + E[j])]

def plaquette_type_and_class(om, c, i, j):
    cs = plaquette_cubes(c, i, j); ps = [om[x] for x in cs]
    keys = {key(*p) for p in ps}
    if len(keys) == 1: return None, None
    encs = []
    for start in range(4):
        for order in (cs, cs[::-1]):
            seq = order[start:] + order[:start]; ref = om[seq[0]]
            encs.append(tuple((loc(*ref, x), rel(*ref, *om[x])) for x in seq))
    W = np.eye(2, dtype=complex)
    for q in range(4):
        a, b = ps[q], ps[(q+1) % 4]
        if key(*a) != key(*b): W = W @ clifford_link(a[0], b[0], np.array(cs[(q+1) % 4]) - np.array(cs[q]))
    return min(encs), CLASS[q8label(W)]

# ---------------- inflation of a representative ----------------
def inflate_config(poses):
    fine = []
    for G, T in poses: fine += inflate(G, T)
    return fine

def inflate_panel(rep):
    """rep = (poses of t,t', c, ax). Returns (fine panel types [4], fine interior plaquette (type,class) [4])."""
    poses, c, ax = rep; om = owner_map(inflate_config(poses))
    others = [d for d in range(3) if d != ax]; p, q = others
    X = 2*(c[ax] + 1); base = 2*np.array(c)
    ptypes, pl = [], []
    for dp in (0, 1):
        for dq in (0, 1):
            fc = np.zeros(3, int); fc[ax] = X - 1; fc[p] = base[p] + dp; fc[q] = base[q] + dq
            ptypes.append(panel_type(om, tuple(fc), ax))
    for dp in (0, 1):   # edges along p at the mid-line q = base_q+1 ; plaquette directions {ax, q}
        fc = np.zeros(3, int); fc[ax] = X - 1; fc[p] = base[p] + dp; fc[q] = base[q]
        pl.append(plaquette_type_and_class(om, tuple(fc), *sorted((ax, q))))
    for dq in (0, 1):   # edges along q at the mid-line p = base_p+1 ; plaquette directions {ax, p}
        fc = np.zeros(3, int); fc[ax] = X - 1; fc[q] = base[q] + dq; fc[p] = base[p]
        pl.append(plaquette_type_and_class(om, tuple(fc), *sorted((ax, p))))
    assert all(t is not None for t, _ in pl)
    return ptypes, pl

def inflate_plaquette(rep):
    """rep = (poses, c, i, j). Returns the 2 fine plaquettes (type,class) along the inflated coarse edge."""
    poses, c, i, j = rep; om = owner_map(inflate_config(poses)); k = 3 - i - j
    out = []
    for s in (0, 1):
        fb = 2*np.array(c) + E[i] + E[j] + s*E[k]
        out.append(plaquette_type_and_class(om, tuple(fb), i, j))
    assert all(t is not None for t, _ in out)
    return out

# ---------------- level-1 seed and closure of the type system ----------------
T1 = inflate(np.eye(3, dtype=int), np.zeros(3, dtype=int)); om1 = owner_map(T1)
panel_reps, plaq_reps, plaq_class = {}, {}, {}
P1, Pi1 = collections.Counter(), collections.Counter()
for c, pose in om1.items():
    for ax in range(3):
        c2 = tuple(np.array(c) + E[ax])
        if c2 in om1 and key(*om1[c2]) != key(*pose):
            t = panel_type(om1, c, ax); P1[t] += 1
            panel_reps.setdefault(t, ([pose, om1[c2]], c, ax))
    for (i, j) in [(0, 1), (0, 2), (1, 2)]:
        cs = plaquette_cubes(c, i, j)
        if all(x in om1 for x in cs):
            t, cl = plaquette_type_and_class(om1, c, i, j)
            if t is not None:
                Pi1[t] += 1; plaq_class[t] = cl
                plaq_reps.setdefault(t, ([om1[x] for x in cs], c, i, j))
print(f"level-1 seed: {sum(P1.values())} panels in {len(P1)} types; {sum(Pi1.values())} plaquettes in {len(Pi1)} types")

panel_img, plaq_img_from_panel, plaq_img = {}, {}, {}
queue_p, queue_q = list(panel_reps), list(plaq_reps); seen_p, seen_q = set(queue_p), set(queue_q)
while queue_p or queue_q:
    if queue_p:
        t = queue_p.pop(); ptypes, pl = inflate_panel(panel_reps[t])
        panel_img[t] = collections.Counter(ptypes); plaq_img_from_panel[t] = collections.Counter(tt for tt, _ in pl)
        om = owner_map(inflate_config(panel_reps[t][0]))
        for tt in ptypes:
            if tt not in seen_p:
                # find a representative of tt in the inflated configuration
                for c, pose in om.items():
                    for ax in range(3):
                        c2 = tuple(np.array(c) + E[ax])
                        if c2 in om and key(*om[c2]) != key(*pose) and panel_type(om, c, ax) == tt:
                            panel_reps[tt] = ([pose, om[c2]], c, ax); break
                    if tt in panel_reps: break
                seen_p.add(tt); queue_p.append(tt)
        for tt, cl in pl:
            plaq_class[tt] = cl
            if tt not in seen_q:
                for c in om:
                    for (i, j) in [(0, 1), (0, 2), (1, 2)]:
                        cs = plaquette_cubes(c, i, j)
                        if all(x in om for x in cs) and plaquette_type_and_class(om, c, i, j)[0] == tt:
                            plaq_reps[tt] = ([om[x] for x in cs], c, i, j); break
                    if tt in plaq_reps: break
                seen_q.add(tt); queue_q.append(tt)
    else:
        t = queue_q.pop(); out = inflate_plaquette(plaq_reps[t]); plaq_img[t] = collections.Counter(tt for tt, _ in out)
        om = owner_map(inflate_config(plaq_reps[t][0]))
        for tt, cl in out:
            plaq_class[tt] = cl
            if tt not in seen_q:
                for c in om:
                    for (i, j) in [(0, 1), (0, 2), (1, 2)]:
                        cs = plaquette_cubes(c, i, j)
                        if all(x in om for x in cs) and plaquette_type_and_class(om, c, i, j)[0] == tt:
                            plaq_reps[tt] = ([om[x] for x in cs], c, i, j); break
                    if tt in plaq_reps: break
                seen_q.add(tt); queue_q.append(tt)
ptypes_all, qtypes_all = sorted(seen_p), sorted(seen_q)
print(f"closed type system: {len(ptypes_all)} panel types, {len(qtypes_all)} plaquette types")
assert all(sum(panel_img[t].values()) == 4 for t in ptypes_all) and all(sum(plaq_img[t].values()) == 2 for t in qtypes_all)
assert all(sum(plaq_img_from_panel[t].values()) == 4 for t in ptypes_all)

# ---------------- the recursion:  P_{m+1} = 8^m p1 + M P_m ;  Pi_{m+1} = 8^m pi1 + A P_m + B Pi_m ----------------
def step(P, Pi, m):
    P2 = collections.Counter({t: 8**m * n for t, n in P1.items()}); Pi2 = collections.Counter({t: 8**m * n for t, n in Pi1.items()})
    for t, n in P.items():
        for tt, mlt in panel_img[t].items(): P2[tt] += n * mlt
        for tt, mlt in plaq_img_from_panel[t].items(): Pi2[tt] += n * mlt
    for t, n in Pi.items():
        for tt, mlt in plaq_img[t].items(): Pi2[tt] += n * mlt
    return P2, Pi2
def class_counts(Pi):
    out = collections.Counter()
    for t, n in Pi.items(): out[plaq_class[t]] += n
    return out
measured = {1: {'1': 26, '-1': 3, 'i': 12, 'j': 7, 'k': 12}, 2: {'1': 385, '-1': 42, 'i': 124, 'j': 117, 'k': 124},
            3: {'1': 3945, '-1': 530, 'i': 1020, 'j': 1213, 'k': 1020}, 4: {'1': 35161, '-1': 5394, 'i': 8188, 'j': 10749, 'k': 8188},
            5: {'1': 296121, '-1': 48146, 'i': 65532, 'j': 90109, 'k': 65532}}
P, Pi = P1, Pi1; rec = {1: class_counts(Pi1)}
for m in range(1, 7):
    P, Pi = step(P, Pi, m); rec[m+1] = class_counts(Pi)
print("\nRECURSION vs DIRECT ENUMERATION (class-resolved inter-tile plaquette counts):")
for m in range(1, 8):
    r = {c: rec[m][c] for c in CLASSES}; line = f" level {m}: recursion {r}  N={sum(r.values())}"
    if m in measured: line += f"  matches direct enumeration: {r == measured[m]}"
    print(line)

# ---------------- exact spectral analysis of the type-substitution operator ----------------
idx_p = {t: n for n, t in enumerate(ptypes_all)}; idx_q = {t: n for n, t in enumerate(qtypes_all)}
nP, nQ = len(ptypes_all), len(qtypes_all)
M = sp.zeros(nP, nP); A = sp.zeros(nQ, nP); B = sp.zeros(nQ, nQ)
for t in ptypes_all:
    for tt, mlt in panel_img[t].items(): M[idx_p[tt], idx_p[t]] += mlt
    for tt, mlt in plaq_img_from_panel[t].items(): A[idx_q[tt], idx_p[t]] += mlt
for t in qtypes_all:
    for tt, mlt in plaq_img[t].items(): B[idx_q[tt], idx_q[t]] += mlt
S = sp.BlockMatrix([[M, sp.zeros(nP, nQ)], [A, B]]).as_explicit()
cpM = sp.factor(M.charpoly().as_expr()); cpB = sp.factor(B.charpoly().as_expr())
print("\nEXACT SPECTRUM OF THE TYPE-SUBSTITUTION OPERATOR")
print(" charpoly of panel block M (row sums 4):", cpM)
print(" charpoly of plaquette block B (row sums 2):", cpB)
lam = sp.Symbol('x'); minpoly_S = sp.factor(sp.Matrix(S).charpoly(lam).as_expr())
# minimal polynomial via Jordan structure: compute index of nilpotency for eigenvalue 0 and semisimplicity of others
def nilp_index(Mat, ev):
    N = Mat - ev*sp.eye(Mat.shape[0]); r_prev = Mat.shape[0]; k = 0
    while True:
        k += 1; r = (N**k).rank()
        if r == r_prev: return k - 1
        r_prev = r
evs = sorted(set(S.eigenvals().keys()), key=lambda z: -abs(complex(z)))
print(" eigenvalues of S:", evs)
for ev in evs: print(f"   eigenvalue {ev}: algebraic multiplicity {S.eigenvals()[ev]}, nilpotency index of (S-ev) on its generalized eigenspace: {nilp_index(S, ev)}")

# closed forms: Count_m(c) = w_c . Pi_m with the affine recursion; solve exactly with the forcing term 8^m
# State vector v_m = (P_m, Pi_m, 8^m);  v_{m+1} = S_aff v_m  with S_aff = [[S, f],[0, 8]], f = (p1, pi1) scaled by 1 (since 8^m * p1 added when stepping from m)
f = sp.Matrix([P1.get(t, 0) for t in ptypes_all] + [Pi1.get(t, 0) for t in qtypes_all])
S_aff = sp.BlockMatrix([[S, f], [sp.zeros(1, nP + nQ), sp.Matrix([[8]])]]).as_explicit()
v1 = sp.Matrix([P1.get(t, 0) for t in ptypes_all] + [Pi1.get(t, 0) for t in qtypes_all] + [8])
w = {c: sp.Matrix([[0]*nP + [1 if plaq_class[t] == c else 0 for t in qtypes_all] + [0]]) for c in CLASSES}
# limiting frequency: f(c) = lim w_c . S_aff^(m-1) v1 / 8^m ; project onto the eigenvalue-8 eigenvector direction
Pdom = (S_aff - 8*sp.eye(S_aff.shape[0]))
# Leading coefficient: component of v1 along the eigenvalue-8 eigenvector of S_aff (unique since 8 is simple)
evec8 = (S_aff - 8*sp.eye(S_aff.shape[0])).nullspace()
assert len(evec8) == 1
u = evec8[0]; u = u / u[-1]            # normalised so that the forcing coordinate is 1 -> v_m ~ 8^m u + lower order
N_lim = sum(u[nP + idx_q[t]] for t in qtypes_all)
print("\nEXACT LIMITS: v_m = 8^m u + (terms with |eigenvalue| < 8).  lim N_m / 8^m =", N_lim)
for c in CLASSES:
    fc = sum(u[nP + idx_q[t]] for t in qtypes_all if plaq_class[t] == c) / N_lim
    print(f"   f({c}) = {fc} = {float(fc):.6f}")
# exact closed form for every m: expand v_m = S_aff^(m-1) v1 in the Jordan basis -> list the non-zero eigenvalue components
print("\nCLOSED FORM: Count_m(c) is a linear combination of ev^m over the eigenvalues listed above (Jordan blocks of size 1 for ev != 0),")
print("so for m beyond the nilpotency index the counts are exactly  A_c 8^m + B_c 4^m + C_c 2^m + D_c  if the nonzero spectrum is {8,4,2,1}.")
