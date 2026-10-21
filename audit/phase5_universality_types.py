"""
Universality test of the type-substitution spectrum across decorations and a periodic-geometry control.
Generic block-substitution engine (doubled coordinates): a geometry is (local doubled cube centres BASE, child ops),
a decoration assigns a permutation to each child.  For each (geometry, decoration) the finite type system of panel
and plaquette types is closed under inflation and the exact characteristic polynomials of the panel block M and the
plaquette block B are computed, together with the exact limiting class frequencies.
Run from the repository root:  python3 -u -I audit/phase5_universality_types.py
"""
import os, sys, itertools, collections, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np, sympy as sp
from independent_clifford_q8_audit import U3, FR30, perm_mat, clifford_link, q8label

E = [np.array(v) for v in ((1,0,0),(0,1,0),(0,0,1))]
CLASS = {'+1': '1', '-1': '-1', '+i': 'i', '-i': 'i', '+j': 'j', '-j': 'j', '+k': 'k', '-k': 'k'}
CLASSES = ['1', '-1', 'i', 'j', 'k']
perms = list(itertools.permutations(range(3)))
even = [p for p in perms if round(np.linalg.det(perm_mat(p))) == 1]; odd = [p for p in perms if round(np.linalg.det(perm_mat(p))) == -1]

def chair_geometry(dec):
    ops = [(perm_mat(dec['0']), np.array([1, 1, 1]))] + [(np.diag([1-2*v[0], 1-2*v[1], 1-2*v[2]]) @ perm_mat(dec[v]), 4*np.array(v)) for v in U3]
    base = [np.array([2*u[0]+1, 2*u[1]+1, 2*u[2]+1]) for u in U3]
    return ops, base
def cube_geometry(dec):   # unit-cube tile, 8 octant children at corners v with frames D_s(v) pi_v
    V8 = list(itertools.product((0, 1), repeat=3))
    ops = [(np.diag([1-2*v[0], 1-2*v[1], 1-2*v[2]]) @ perm_mat(dec[v]), 2*np.array(v)) for v in V8]
    return ops, [np.array([1, 1, 1])]

def analyse(name, ops, base, verbose=True):
    t0 = time.time()
    def inflate(G, T): return [(G @ g, 2*T + G @ t) for g, t in ops]
    def cubes(G, T): return [tuple((G @ bc + 2*T - 1) // 2) for bc in base]
    def key(G, T): return (tuple(map(tuple, G)), tuple(T))
    def owner_map(poses):
        om = {}
        for (G, T) in poses:
            for c in cubes(G, T): om[c] = (G, T)
        return om
    def rel(Gr, Tr, G, T): return (tuple(map(tuple, Gr.T @ G)), tuple(Gr.T @ (T - Tr)))
    def loc(Gr, Tr, c): return tuple(Gr.T @ (2*np.array(c) + 1 - 2*Tr))
    def panel_type(om, c, ax):
        c2 = tuple(np.array(c) + E[ax]); p, p2 = om[c], om[c2]
        return min((loc(*p, c), tuple(p[0].T @ E[ax]), rel(*p, *p2)), (loc(*p2, c2), tuple(p2[0].T @ (-E[ax])), rel(*p2, *p)))
    def pcubes(c, i, j): return [tuple(c), tuple(np.array(c)+E[i]), tuple(np.array(c)+E[i]+E[j]), tuple(np.array(c)+E[j])]
    def plaq(om, c, i, j):
        cs = pcubes(c, i, j); ps = [om[x] for x in cs]
        if len({key(*p) for p in ps}) == 1: return None, None
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
    def inflate_config(poses):
        out = []
        for G, T in poses: out += inflate(G, T)
        return out
    def all_panels(om):
        for c, pose in om.items():
            for ax in range(3):
                c2 = tuple(np.array(c) + E[ax])
                if c2 in om and key(*om[c2]) != key(*pose): yield c, ax
    def all_plaqs(om):
        for c in om:
            for (i, j) in [(0, 1), (0, 2), (1, 2)]:
                if all(x in om for x in pcubes(c, i, j)):
                    t, cl = plaq(om, c, i, j)
                    if t is not None: yield c, i, j, t, cl
    def inflate_panel(rep):
        poses, c, ax = rep; om = owner_map(inflate_config(poses)); p, q = [d for d in range(3) if d != ax]
        X = 2*(c[ax]+1); b = 2*np.array(c); pt, pl = [], []
        for dp in (0, 1):
            for dq in (0, 1):
                fc = np.zeros(3, int); fc[ax] = X-1; fc[p] = b[p]+dp; fc[q] = b[q]+dq; pt.append(panel_type(om, tuple(fc), ax))
        for dp in (0, 1):
            fc = np.zeros(3, int); fc[ax] = X-1; fc[p] = b[p]+dp; fc[q] = b[q]; pl.append(plaq(om, tuple(fc), *sorted((ax, q))))
        for dq in (0, 1):
            fc = np.zeros(3, int); fc[ax] = X-1; fc[q] = b[q]+dq; fc[p] = b[p]; pl.append(plaq(om, tuple(fc), *sorted((ax, p))))
        return pt, pl, om
    def inflate_plaq(rep):
        poses, c, i, j = rep; om = owner_map(inflate_config(poses)); k = 3-i-j
        return [plaq(om, tuple(2*np.array(c) + E[i] + E[j] + s*E[k]), i, j) for s in (0, 1)], om
    T1 = inflate(np.eye(3, dtype=int), np.zeros(3, dtype=int)); om1 = owner_map(T1)
    assert len(om1) == len(base) * len(ops), "children overlap"
    preps, qreps, qclass = {}, {}, {}; P1, Pi1 = collections.Counter(), collections.Counter()
    for c, ax in all_panels(om1):
        t = panel_type(om1, c, ax); P1[t] += 1; preps.setdefault(t, ([om1[c], om1[tuple(np.array(c)+E[ax])]], c, ax))
    for c, i, j, t, cl in all_plaqs(om1):
        Pi1[t] += 1; qclass[t] = cl; qreps.setdefault(t, ([om1[x] for x in pcubes(c, i, j)], c, i, j))
    pimg, qimg_p, qimg = {}, {}, {}; qp, qq = list(preps), list(qreps); sp_, sq = set(qp), set(qq)
    def find_reps(om):
        for c, ax in all_panels(om):
            t = panel_type(om, c, ax)
            if t not in sp_: sp_.add(t); qp.append(t); preps[t] = ([om[c], om[tuple(np.array(c)+E[ax])]], c, ax)
        for c, i, j, t, cl in all_plaqs(om):
            qclass[t] = cl
            if t not in sq: sq.add(t); qq.append(t); qreps[t] = ([om[x] for x in pcubes(c, i, j)], c, i, j)
    while qp or qq:
        if qp:
            t = qp.pop(); pt, pl, om = inflate_panel(preps[t]); pimg[t] = collections.Counter(pt); qimg_p[t] = collections.Counter(tt for tt, _ in pl); find_reps(om)
        else:
            t = qq.pop(); out, om = inflate_plaq(qreps[t]); qimg[t] = collections.Counter(tt for tt, _ in out); find_reps(om)
    pts, qts = sorted(sp_), sorted(sq); ip = {t: n for n, t in enumerate(pts)}; iq = {t: n for n, t in enumerate(qts)}
    nP, nQ = len(pts), len(qts); M = sp.zeros(nP, nP); A = sp.zeros(nQ, nP); B = sp.zeros(nQ, nQ)
    for t in pts:
        for tt, m in pimg[t].items(): M[ip[tt], ip[t]] += m
        for tt, m in qimg_p[t].items(): A[iq[tt], ip[t]] += m
    for t in qts:
        for tt, m in qimg[t].items(): B[iq[tt], iq[t]] += m
    lam = sp.Symbol('lambda'); cpM = sp.factor(M.charpoly(lam).as_expr()); cpB = sp.factor(B.charpoly(lam).as_expr())
    S = sp.BlockMatrix([[M, sp.zeros(nP, nQ)], [A, B]]).as_explicit()
    f = sp.Matrix([P1.get(t, 0) for t in pts] + [Pi1.get(t, 0) for t in qts])
    Saff = sp.BlockMatrix([[S, f], [sp.zeros(1, nP+nQ), sp.Matrix([[8]])]]).as_explicit()
    ns = (Saff - 8*sp.eye(nP+nQ+1)).nullspace(); u = ns[0] / ns[0][-1]
    Nlim = sum(u[nP+iq[t]] for t in qts); freqs = {c: sp.Rational(sum(u[nP+iq[t]] for t in qts if qclass[t] == c)) / sp.Rational(Nlim) for c in CLASSES}
    hol = sorted({qclass[t] for t in qts})
    print(f"[{name}] panels@1={sum(P1.values())} plaquettes@1={sum(Pi1.values())} types: {nP} panel, {nQ} plaquette  ({time.time()-t0:.0f}s)")
    print(f"   charpoly M: {cpM}\n   charpoly B: {cpB}")
    print(f"   lim N_m/8^m = {Nlim}; limiting class frequencies: {freqs}; classes present: {hol}", flush=True)
    return cpM, cpB, freqs

ACHIRAL = {k: (0, 1, 2) for k in FR30}
CANON = {'0': (0,1,2), (0,0,0): (0,1,2), (0,0,1): (0,2,1), (0,1,0): (0,2,1), (0,1,1): (0,1,2), (1,0,0): (0,2,1), (1,0,1): (0,1,2), (1,1,0): (0,1,2)}
rng = np.random.default_rng(2026)
def random_dec():
    d = {'0': even[rng.integers(3)]}
    for v in U3: d[v] = (even if sum(v) % 2 == 0 else odd)[rng.integers(3)]
    return d
analyse("chair / FR30", *chair_geometry(FR30))
analyse("chair / achiral (D_s only, det -1 frames)", *chair_geometry(ACHIRAL))
analyse("chair / canonical homochiral", *chair_geometry(CANON))
for r in range(6): analyse(f"chair / random admissible decoration #{r}", *chair_geometry(random_dec()))
V8 = list(itertools.product((0, 1), repeat=3))
cube_fr30 = {v: FR30.get(v, (0, 2, 1)) for v in V8}            # (1,1,1) needs an odd permutation
cube_rand = {v: (even if sum(v) % 2 == 0 else odd)[rng.integers(3)] for v in V8}
cube_achiral = {v: (0, 1, 2) for v in V8}
analyse("unit-cube block substitution (periodic geometry) / FR30-type decoration", *cube_geometry(cube_fr30))
analyse("unit-cube block substitution / random admissible decoration", *cube_geometry(cube_rand))
analyse("unit-cube block substitution / achiral D_s decoration", *cube_geometry(cube_achiral))
