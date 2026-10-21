"""
Phase 5B / Workstream E, task E3: exact limit frequencies of CORRELATED local objects from the type recursion.

Part A -- box objects.  A "box object" is an axis-aligned box of unit cubes (all present, >= 2 owner tiles) with its
owner tiles and their frames, modulo Gamma = SO(3,Z) x Z^3.  Shapes: P = 1x1x2 (inter-tile panel), Q = 1x2x2 (the 4
cubes around a lattice edge = plaquette), R = 1x2x3 (two parallel plaquettes sharing a panel), W = 1x3x3 (the 2x2
rectangle of 4 parallel lattice edges; its boundary is an 8-cube loop), V = 2x2x2 (the 8 cubes around a lattice
point; contains the 6 plaquettes incident to the point).  Coarse parents of a box are a box of smaller or equal shape
(row of length 1 -> 1 parent, 2 -> 1 or 2 parents, 3 -> exactly 2 parents), so, exactly as in the parity trichotomy of
PHASE5A_RECURSION_THEOREM.md Statement 1, the counts in the supertiles satisfy, for all m >= 1,
      v^Y_{m+1} = 8^m f_Y + sum_{Y'} S_{Y Y'} v^{Y'}_m ,
with f_Y = v^Y_1 (objects whose parents lie in one tile = objects inside one inflated tile, each a rigid copy of T_1)
and S_{Y Y'}[tau', tau] = number of fine objects of type tau' whose parent set is exactly the cube set of the coarse
object tau.  Dependencies: P <- P;  Q <- P, Q;  V <- P, Q, V;  R <- P, Q;  W <- Q.  All matrices are computed from the
inflated type patches, the recursion is verified exactly against direct enumeration of T_2, T_3, T_4, and the limits
      u_Y = lim 8^-m v^Y_m   (exact rationals, Statement 2/3 of the recursion theorem; rho(S_YY) < 8)
are solved exactly.  Class observables (functions of the type): the holonomy class of each plaquette (Q8 conjugacy
classes {1}, {-1}, {+-i}, {+-j}, {+-k}), the joint classes of the two plaquettes of R, of the four plaquettes of W and
of the 8-cube boundary loop of W, of the six plaquettes of V.

Part B -- 1-star and 2-star type frequencies.  The collared substitution Phi (72x72, column sums 8) acts on the legal
1-star types; the limit frequencies u_1 of the 1-star types are the unique vector with Phi u_1 = 8 u_1, sum = 1 (unique
if the eigenvalue 8 of Phi is simple -- verified exactly, together with the absence of other eigenvalues of modulus 8).
The per-tile distribution of the number of plaquettes of class -1 among the 48 inter-tile plaquettes touching a tile,
and the 2-star frequencies u_2 = Phi_2 u_1 / 8, follow.  Cross-check: the plaquette class frequencies recovered from
u_1 (counting each plaquette with weight 1/#tiles around it) must equal 18 x (Theorem A class frequencies).

Run from the repository root:  OMP_NUM_THREADS=1 python3 -u -I audit/phase5b_e_recursion_correlations.py
Output: audit/results/phase5b_e_recursion_correlations.txt
"""
import os, sys, time, itertools, collections, resource
from fractions import Fraction
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from independent_clifford_q8_audit import FR30, U3, perm_mat, clifford_link, q8label

OUT = []; T_START = time.time()
RESF = os.path.join(HERE, 'results', 'phase5b_e_recursion_correlations.txt')
def say(*a):
    s = " ".join(str(x) for x in a); print(s, flush=True); OUT.append(s)
    with open(RESF, 'w') as f: f.write("\n".join(OUT) + "\n")
def rss(): return resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 1e6
def F(*a): return Fraction(*a)

# ------------------------------------------------------------------------------------------------ substitution data
ops = [(perm_mat(FR30['0']), np.array([1, 1, 1]))]
for v in U3:
    ops.append((np.diag([1 - 2 * v[0], 1 - 2 * v[1], 1 - 2 * v[2]]) @ perm_mat(FR30[v]), 4 * np.array(v)))
GOPS = np.array([g for g, t in ops]); TOPS = np.array([t for g, t in ops])
LB = np.array([[2 * u[0] + 1, 2 * u[1] + 1, 2 * u[2] + 1] for u in U3])
I3 = np.eye(3, dtype=int)
def key(M): return tuple(int(x) for x in np.asarray(M).ravel())
Gs = [I3.copy()]; gidx = {key(I3): 0}; fr = [I3]
while fr:
    new = []
    for M in fr:
        for g in GOPS:
            P = M @ g
            if key(P) not in gidx: gidx[key(P)] = len(Gs); Gs.append(P); new.append(P)
    fr = new
Gs = np.array(Gs); NG = len(Gs); assert NG == 24
MULT = np.array([[gidx[key(Gs[i] @ Gs[j])] for j in range(NG)] for i in range(NG)])
INV = np.array([gidx[key(Gs[i].T)] for i in range(NG)])
Q8 = ['+1', '-1', '+i', '-i', '+j', '-j', '+k', '-k']
LINK = np.zeros((NG, NG, 3, 2, 2), complex)
for a in range(NG):
    for b in range(NG):
        for ax in range(3):
            nv = np.zeros(3, int); nv[ax] = 1; LINK[a, b, ax] = clifford_link(Gs[a], Gs[b], nv)
CLASS = {'+1': '1', '-1': '-1', '+i': 'i', '-i': 'i', '+j': 'j', '-j': 'j', '+k': 'k', '-k': 'k'}
CLASSES = ['1', '-1', 'i', 'j', 'k']
_LUT = np.full(3 ** 9, -1, np.int8)
for i in range(NG): _LUT[int((((Gs[i].ravel() + 1) * (3 ** np.arange(9))).sum()))] = i
def frame_index(G):
    flat = np.asarray(G).reshape(len(G), 9).astype(np.int64); out = _LUT[((flat + 1) * (3 ** np.arange(9))).sum(1)]
    assert (out >= 0).all(); return out.astype(np.int64)
def gen_poses(level):
    G = I3[None].astype(np.int64); T = np.zeros((1, 3), np.int64)
    for _ in range(level):
        G2 = np.einsum('nij,cjk->ncik', G, GOPS).reshape(-1, 3, 3)
        T2 = (2 * T[:, None, :] + np.einsum('nij,cj->nci', G, TOPS)).reshape(-1, 3)
        G, T = G2, T2
    return G.astype(np.int64), T.astype(np.int64)
def cubes_of_poses(G, T, odd=LB):
    return (np.einsum('nij,kj->nki', G.astype(np.int64), odd) + 2 * T[:, None, :].astype(np.int64) - 1) // 2
def owner_grid(N, G, T):
    grid = np.full((N, N, N), -1, np.int32); cubes = cubes_of_poses(G, T)
    assert cubes.min() >= 0 and cubes.max() < N
    flat = cubes.reshape(-1, 3); grid[flat[:, 0], flat[:, 1], flat[:, 2]] = np.repeat(np.arange(len(G), dtype=np.int32), 7)
    assert (grid >= 0).sum() == 7 * len(G); return grid

# ------------------------------------------------------------------------------------------------ canonical codes
def canon_keys(cubes, owners, G, T, fidx):
    """cubes (n, k, 3) int corners, owners (n, k) tile indices into pose arrays G (.,3,3), T (.,3), fidx (.,).
    Returns list of n canonical keys (bytes), Gamma-invariant: min over base tiles of the sorted encoded cube list."""
    n, k, _ = cubes.shape
    allrows = []
    for j in range(k):
        b = owners[:, j]; Mb = Gs[fidx[b]]; Tb = T[b]
        relc = (np.einsum('nji,nkj->nki', Mb, 2 * cubes + 1 - 2 * Tb[:, None, :]) - 1) // 2        # Mb^T (2c+1-2Tb), then corner
        relf = MULT[INV[fidx[b]][:, None], fidx[owners]]                                            # (n,k)
        relt = np.einsum('nji,nkj->nki', Mb, T[owners] - Tb[:, None, :])                            # (n,k,3)
        assert (np.abs(relc) <= 8).all() and (np.abs(relt) <= 16).all()
        code = ((((((relc[..., 0] + 8) * 17 + relc[..., 1] + 8) * 17 + relc[..., 2] + 8) * 24 + relf) * 33 + relt[..., 0] + 16) * 33 + relt[..., 1] + 16) * 33 + relt[..., 2] + 16
        allrows.append(np.sort(code, axis=1))
    rows = np.stack(allrows, axis=1).astype('>i8')        # (n, k, k)
    keys = []
    for i in range(n):
        keys.append(min(rows[i, j].tobytes() for j in range(k)))
    return keys

SHAPES = {'P': (1, 1, 2), 'Q': (1, 2, 2), 'R': (1, 2, 3), 'W': (1, 3, 3), 'V': (2, 2, 2)}
PARENTS = {'P': ['P'], 'Q': ['P', 'Q'], 'R': ['P', 'Q'], 'W': ['Q'], 'V': ['P', 'Q', 'V']}
ORDER = ['P', 'Q', 'V', 'R', 'W']
def orientations(dims): return sorted(set(itertools.permutations(dims)))
def box_offsets(d): return np.array(list(itertools.product(range(d[0]), range(d[1]), range(d[2]))))

def enumerate_boxes(shape, G, T, fidx, grid):
    """all placements of the shape (all orientations) with all cubes present and >= 2 owners; returns Counter of
    canonical keys -> count and a representative (owner poses, cube list) per key."""
    N = grid.shape[0]; cnt = collections.Counter(); rep = {}
    for d in orientations(SHAPES[shape]):
        offs = box_offsets(d)
        xs = np.array(list(itertools.product(range(N - d[0] + 1), range(N - d[1] + 1), range(N - d[2] + 1))))
        for s in range(0, len(xs), 200000):
            X = xs[s:s+200000]; cubes = X[:, None, :] + offs[None]
            O = grid[cubes[..., 0], cubes[..., 1], cubes[..., 2]]
            ok = (O >= 0).all(1) & ((O != O[:, :1]).any(1))
            cubes, O = cubes[ok], O[ok]
            if len(O) == 0: continue
            keys = canon_keys(cubes, O, G, T, fidx)
            for i, kk in enumerate(keys):
                cnt[kk] += 1
                if kk not in rep:
                    tl = sorted(set(O[i].tolist()))
                    rep[kk] = ([(Gs[fidx[t]].copy(), T[t].copy()) for t in tl], [tuple(int(x) for x in c) for c in cubes[i]], [tl.index(o) for o in O[i]])
    return cnt, rep

def inflation_children(rep):
    """fine objects (all shapes) whose parent cube set is exactly the coarse object's cube set; returns Counter
    (shape, canonical key) -> count and representatives."""
    poses, ccubes, _ = rep
    fine = [(g @ gg, 2 * t + g @ tt) for g, t in poses for gg, tt in ops]
    Gf = np.array([g for g, t in fine]); Tf = np.array([t for g, t in fine]); ff = frame_index(Gf)
    own = {}
    for a, c in enumerate(cubes_of_poses(Gf, Tf).reshape(-1, 3)):
        own[tuple(int(x) for x in c)] = a // 7
    region = sorted({(2 * c[0] + d[0], 2 * c[1] + d[1], 2 * c[2] + d[2]) for c in ccubes for d in itertools.product((0, 1), repeat=3)})
    cset = set(ccubes); rset = set(region); out = collections.Counter(); reps = {}
    lo = np.min(region, axis=0); hi = np.max(region, axis=0)
    for shape in ORDER:
        for d in orientations(SHAPES[shape]):
            offs = box_offsets(d); cand = []
            for x in itertools.product(*[range(lo[i], hi[i] - d[i] + 2) for i in range(3)]):
                cubes = [(x[0] + o[0], x[1] + o[1], x[2] + o[2]) for o in offs]
                if not all(q in rset for q in cubes): continue
                if {(q[0] // 2, q[1] // 2, q[2] // 2) for q in cubes} != cset: continue
                cand.append(cubes)
            if not cand: continue
            cubes = np.array(cand); O = np.array([[own[q] for q in cl] for cl in cand])
            assert ((O != O[:, :1]).any(1)).all()
            keys = canon_keys(cubes, O, Gf, Tf, ff)
            for i, kk in enumerate(keys):
                out[(shape, kk)] += 1
                if (shape, kk) not in reps:
                    tl = sorted(set(O[i].tolist()))
                    reps[(shape, kk)] = ([(Gf[t].copy(), Tf[t].copy()) for t in tl], [tuple(int(x) for x in c) for c in cubes[i]], [tl.index(o) for o in O[i]])
    return out, reps

def holonomy_class(loop_cubes, rep):
    """class of the ordered product of links around a cyclic list of adjacent cubes of the representative."""
    poses, ccubes, lab = rep; owner = {c: lab[i] for i, c in enumerate(ccubes)}
    fid = [gidx[key(g)] for g, t in poses]
    W = np.eye(2, dtype=complex)
    for s in range(len(loop_cubes)):
        q1, q2 = loop_cubes[s], loop_cubes[(s + 1) % len(loop_cubes)]
        t1, t2 = owner[q1], owner[q2]
        if t1 == t2: continue
        d = np.array(q2) - np.array(q1); ax = int(np.nonzero(d)[0][0]); assert abs(d).sum() == 1
        W = W @ LINK[fid[t1], fid[t2], ax]
    name = q8label(W); assert name != 'other'; return CLASS[name]
def square_loop(cubes4):
    """cyclic order of the 4 cubes of a 1x2x2 box."""
    c = sorted(cubes4); lo = c[0]; axes = [i for i in range(3) if any(q[i] != lo[i] for q in c)]
    i, j = axes
    def at(a, b):
        q = list(lo); q[i] += a; q[j] += b; return tuple(q)
    return [at(0, 0), at(1, 0), at(1, 1), at(0, 1)]
def sub_squares(ccubes):
    """all 1x2x2 sub-boxes (as cyclic loops) of a box object, sorted."""
    cs = set(ccubes); out = []
    for q in ccubes:
        for i, j in [(0, 1), (0, 2), (1, 2)]:
            sq = []
            for a, b in [(0, 0), (1, 0), (1, 1), (0, 1)]:
                p = list(q); p[i] += a; p[j] += b; sq.append(tuple(p))
            if all(p in cs for p in sq): out.append(sq)
    return out
def class_observable(shape, rep):
    poses, ccubes, lab = rep
    sqs = sub_squares(ccubes); cls = [holonomy_class(sq, rep) for sq in sqs]
    if shape == 'Q': return cls[0]
    if shape == 'R': return tuple(sorted(cls))
    if shape == 'W':
        c = sorted(ccubes); lo = c[0]; axes = [i for i in range(3) if any(q[i] != lo[i] for q in c)]; i, j = axes
        ring = []
        for a, b in [(0, 0), (1, 0), (2, 0), (2, 1), (2, 2), (1, 2), (0, 2), (0, 1)]:
            p = list(lo); p[i] += a; p[j] += b; ring.append(tuple(p))
        return (tuple(sorted(cls)), holonomy_class(ring, rep))
    if shape == 'V': return tuple(sorted(cls))
    return None

# ------------------------------------------------------------------------------------------------ Part A
say("PHASE 5B-E / E3: exact limit frequencies of correlated local objects from the type recursion")
say(f"started {time.strftime('%Y-%m-%d %H:%M:%S')}; OMP_NUM_THREADS={os.environ.get('OMP_NUM_THREADS')}")
say("=" * 100); say("A. BOX-OBJECT TYPE SYSTEMS P (1x1x2), Q (1x2x2), V (2x2x2), R (1x2x3), W (1x3x3): closure, recursion, exact limits")
t0 = time.time()
counts = {}; reps = {}
for m in range(1, 5):
    G, T = gen_poses(m); fidx = frame_index(G); grid = owner_grid(2 ** (m + 1), G, T)
    counts[m] = {}
    for shape in ORDER:
        cnt, rp = enumerate_boxes(shape, G, T, fidx, grid); counts[m][shape] = cnt
        for kk, r in rp.items(): reps.setdefault((shape, kk), r)
    say(f" T_{m}: inter-tile box objects " + ", ".join(f"{s}: {sum(counts[m][s].values())} ({len(counts[m][s])} types)" for s in ORDER) + f"  ({time.time()-t0:.0f}s)")
# inflation closure of the type sets
types = {s: set(k for (sh, k) in reps if sh == s) for s in ORDER}
S = collections.defaultdict(int)              # S[(shape', key'), (shape, key)] = count
todo = list(reps.keys()); done = set(); rounds = 0
while todo:
    rounds += 1; new = []
    for tk in todo:
        if tk in done: continue
        done.add(tk)
        ch, chreps = inflation_children(reps[tk])
        for ck, c in ch.items():
            S[(ck, tk)] += c
            if ck not in reps: reps[ck] = chreps[ck]; new.append(ck); types[ck[0]].add(ck[1])
    todo = new
say(f" inflation closure of the type sets after {rounds} rounds: " + ", ".join(f"{s}: {len(types[s])} types" for s in ORDER) + f"  ({time.time()-t0:.0f}s)")
TYPES = {s: sorted(types[s]) for s in ORDER}; IDX = {s: {k: i for i, k in enumerate(TYPES[s])} for s in ORDER}
def mat(sf, sc):
    M = np.zeros((len(TYPES[sf]), len(TYPES[sc])), dtype=object)
    for i in range(M.shape[0]):
        for j in range(M.shape[1]): M[i, j] = 0
    for ((shf, kf), (shc, kc)), c in S.items():
        if shf == sf and shc == sc: M[IDX[sf][kf], IDX[sc][kc]] += c
    return M
MAT = {(sf, sc): mat(sf, sc) for sf in ORDER for sc in ORDER}
for sf in ORDER:
    for sc in ORDER:
        tot = int(sum(int(x) for x in MAT[(sf, sc)].ravel()))
        if tot and sc not in PARENTS[sf]: say(f"   UNEXPECTED dependency {sf} <- {sc}")
for sf in ORDER:
    for sc in PARENTS[sf]:
        cs = sorted({int(sum(int(x) for x in MAT[(sf, sc)][:, j])) for j in range(len(TYPES[sc]))})
        say(f"   S_{sf}{sc}: {MAT[(sf, sc)].shape}, column sums {cs}")
def vec(m, s): return [counts[m][s].get(k, 0) for k in TYPES[s]]
# exact recursion check m -> m+1 for m = 1, 2, 3
for m in range(1, 4):
    ok_all = True
    for sf in ORDER:
        pred = [8 ** m * x for x in vec(1, sf)]
        for sc in PARENTS[sf]:
            vc = vec(m, sc); Mm = MAT[(sf, sc)]
            for i in range(len(pred)): pred[i] += sum(int(Mm[i, j]) * vc[j] for j in range(len(vc)) if Mm[i, j])
        ok = pred == vec(m + 1, sf); ok_all &= ok
    say(f" exact recursion v_{m+1} = 8^{m} f + sum S v_{m} verified coordinate-wise for all five shapes: {ok_all}")
    assert ok_all
# exact limits
from sympy import Matrix, Rational, eye, factor, symbols
def solve_limit(sf, rhs):
    A = Matrix(len(TYPES[sf]), len(TYPES[sf]), lambda i, j: 8 * (i == j) - int(MAT[(sf, sf)][i, j]))
    sol = A.LUsolve(Matrix([Rational(x.numerator, x.denominator) for x in rhs]))
    return [Fraction(int(x.p), int(x.q)) for x in sol]
U = {}
for sf in ORDER:
    rhs = [F(x) for x in vec(1, sf)]
    for sc in PARENTS[sf]:
        if sc == sf: continue
        Mm = MAT[(sf, sc)]; uc = U[sc]
        for i in range(len(rhs)): rhs[i] += sum(F(int(Mm[i, j])) * uc[j] for j in range(len(uc)) if Mm[i, j])
    U[sf] = solve_limit(sf, rhs) if sf in PARENTS[sf] else [x / 8 for x in rhs]
    tot = sum(U[sf]); den = max(x.denominator for x in U[sf])
    lam = symbols('lambda')
    cp = factor(Matrix(len(TYPES[sf]), len(TYPES[sf]), lambda i, j: int(MAT[(sf, sf)][i, j])).charpoly(lam).as_expr()) if sf in PARENTS[sf] else None
    say(f" {sf}: limit per tile sum u = {tot} = {float(tot):.6f}; max denominator {den}; charpoly(S_{sf}{sf}) = {cp}  ({time.time()-t0:.0f}s)")
    # finite-size check: 8^-m v_m -> u (print the relative deviation at m = 4)
    v4 = vec(4, sf); dev = max(abs(F(v4[i], 8 ** 4) - U[sf][i]) for i in range(len(v4)))
    say(f"     max |8^-4 v_4 - u| over types = {float(dev):.3e}  (expected O(2^-4..4^-4) surface corrections)")
# class observables
say("-" * 100); say(" class observables (exact rational limits, per tile):")
obs = {}
for sf in ORDER:
    if sf == 'P': continue
    dist = collections.defaultdict(Fraction)
    for i, k in enumerate(TYPES[sf]): dist[class_observable(sf, reps[(sf, k)])] += U[sf][i]
    obs[sf] = dist
qd = obs['Q']; tq = sum(qd.values())
say(f" Q (plaquettes): total {tq} per tile; class frequencies " + ", ".join(f"{c}: {qd[c]/tq}" for c in CLASSES))
say(f"   Theorem A (PHASE5A_RECURSION_THEOREM.md): 18 per tile; 19/36, 13/144, 1/9, 23/144, 1/9  -> agreement: {tq == 18 and [qd[c]/tq for c in CLASSES] == [F(19,36), F(13,144), F(1,9), F(23,144), F(1,9)]}")
rd = obs['R']; tr = sum(rd.values())
say(f" R (two parallel plaquettes sharing a panel): total {tr} per tile (= {float(tr):.4f}); joint class distribution (unordered pair):")
pq = {c: qd[c] / tq for c in CLASSES}
for pair in sorted(rd, key=lambda p: -rd[p]):
    indep = (2 if pair[0] != pair[1] else 1) * pq[pair[0]] * pq[pair[1]]
    say(f"     {str(pair):14s} {str(rd[pair]/tr):>22s} = {float(rd[pair]/tr):.6f}   (independent-marginals prediction {float(indep):.6f}, ratio {float(rd[pair]/tr/indep) if indep else float('nan'):.3f})")
say(f"   marginal of one plaquette of the pair: " + ", ".join(f"{c}: {sum(rd[p]*(p.count(c)) for p in rd)/(2*tr)}" for c in CLASSES) + "  (must equal the single-plaquette frequencies: "
    f"{all(sum(rd[p]*p.count(c) for p in rd)/(2*tr) == pq[c] for c in CLASSES)})")
wd = obs['W']; tw = sum(wd.values())
loop = collections.defaultdict(Fraction)
for (cls4, ring), v in wd.items(): loop[ring] += v
say(f" W (2x2 rectangle of 4 parallel plaquettes; 8-cube boundary loop): total {tw} per tile; class of the loop holonomy: " + ", ".join(f"{c}: {loop[c]/tw} = {float(loop[c]/tw):.6f}" for c in CLASSES))
n_minus = collections.defaultdict(Fraction)
for (cls4, ring), v in wd.items(): n_minus[cls4.count('-1')] += v
say(f"   number of class -1 plaquettes among the 4: " + ", ".join(f"{n}: {n_minus[n]/tw} = {float(n_minus[n]/tw):.5f}" for n in sorted(n_minus)))
vd = obs['V']; tv = sum(vd.values())
n6 = collections.defaultdict(Fraction); nontriv = collections.defaultdict(Fraction)
for cls6, v in vd.items(): n6[cls6.count('-1')] += v; nontriv[6 - cls6.count('1')] += v
say(f" V (8 cubes around a lattice point; 6 incident plaquettes): total {tv} per tile (every lattice point is inter-tile: 7 per tile expected: {tv == 7})")
say(f"   number of class -1 plaquettes among the 6: " + ", ".join(f"{n}: {n6[n]/tv} = {float(n6[n]/tv):.5f}" for n in sorted(n6)))
say(f"   number of non-flat plaquettes among the 6: " + ", ".join(f"{n}: {nontriv[n]/tv} = {float(nontriv[n]/tv):.5f}" for n in sorted(nontriv)))
say(f"   mean number of -1 plaquettes per lattice point {sum(n*v for n, v in n6.items())/tv} (independent check: 6 x 13/144 = {F(6*13,144)}; equality is forced since each plaquette is incident to 2 lattice points: {sum(n*v for n, v in n6.items())/tv == F(78,144)})")
say(f" wall time Part A {time.time()-t0:.0f}s, rss {rss():.2f} GB")

# ------------------------------------------------------------------------------------------------ Part B
say("=" * 100); say("B. 1-STAR AND 2-STAR TYPE FREQUENCIES FROM THE COLLARED SUBSTITUTION; PER-TILE -1 PLAQUETTE COUNT")
t0 = time.time()
L1 = [l for l in itertools.product((-1, 0, 1, 2), repeat=3) if l != (2, 2, 2)]; L1ODD = 2 * np.array(L1) + 1
L2 = [l for l in itertools.product((-2, -1, 0, 1, 2, 3), repeat=3) if l != (3, 3, 3)]; L2ODD = 2 * np.array(L2) + 1
R_ENC = 16; K_ENC = 33
def encode(rf, rel): return ((rf * K_ENC + rel[..., 0] + R_ENC) * K_ENC + rel[..., 1] + R_ENC) * K_ENC + rel[..., 2] + R_ENC
def decode(code):
    code = int(code); dz = code % K_ENC - R_ENC; code //= K_ENC; dy = code % K_ENC - R_ENC; code //= K_ENC
    return code // K_ENC, (code % K_ENC - R_ENC, dy, dz)
def lookup(grid, P):
    N = grid.shape[0]; inside = ((P >= 0) & (P < N)).all(-1); Pc = np.where(inside[..., None], P, 0)
    return np.where(inside, grid[Pc[..., 0], Pc[..., 1], Pc[..., 2]], -1)
def star_census(G, T, grid, odd):
    fi = frame_index(G); cnt = collections.Counter(); N = len(G)
    for s in range(0, N, 8192):
        sl = slice(s, min(N, s + 8192)); O = lookup(grid, cubes_of_poses(G[sl], T[sl], odd)); comp = (O >= 0).all(1)
        idx = np.nonzero(comp)[0]
        if len(idx) == 0: continue
        Oc = O[idx]; a = idx + s
        rf = MULT[INV[fi[a]][:, None], fi[Oc]]
        rel = np.einsum('nji,nkj->nki', G[a], T[Oc] - T[a][:, None, :])
        codes = np.sort(encode(rf, rel), axis=1); uniq, c = np.unique(codes, axis=0, return_counts=True)
        for row, cc in zip(uniq, c): cnt[frozenset(int(x) for x in row)] += int(cc)
    return cnt
def poses_from_key(k):
    poses = [(Gs[decode(c)[0]].copy(), np.array(decode(c)[1])) for c in sorted(k)]
    center = [i for i, (g, t) in enumerate(poses) if key(g) == key(I3) and tuple(t) == (0, 0, 0)]; assert len(center) == 1
    return poses, center[0]
def owner_dict(poses):
    own = {}
    for a, (g, t) in enumerate(poses):
        for c in cubes_of_poses(g[None], t[None])[0]: own[tuple(int(x) for x in c)] = a
    return own
def star_key(poses, own, center, odd):
    g0, t0 = poses[center]; mem = set()
    for c in cubes_of_poses(g0[None], t0[None], odd)[0]:
        o = own.get(tuple(int(x) for x in c))
        if o is None: return None
        mem.add(o)
    return frozenset(int(encode(gidx[key(g0.T @ poses[b][0])], g0.T @ (poses[b][1] - t0))) for b in mem)
def Phi_r(k, odd):
    poses, center = poses_from_key(k); fine = [(g @ gg, 2 * t + g @ tt) for g, t in poses for gg, tt in ops]; own = owner_dict(fine)
    out = [star_key(fine, own, 8 * center + c, odd) for c in range(8)]; assert None not in out; return out
G4, T4 = gen_poses(4); grid4 = owner_grid(32, G4, T4); c1_4 = star_census(G4, T4, grid4, L1ODD)
seed = max(c1_4, key=c1_4.get); V1 = {seed}; frontier = [seed]
while frontier:
    new = []
    for k in frontier:
        for kk in Phi_r(k, L1ODD):
            if kk not in V1: V1.add(kk); new.append(kk)
    frontier = new
V1 = sorted(V1, key=lambda k: sorted(k)); I1 = {k: i for i, k in enumerate(V1)}; assert len(V1) == 72
PHI = Matrix.zeros(72, 72)
for k in V1:
    for kk in Phi_r(k, L1ODD): PHI[I1[kk], I1[k]] += 1
say(f" Phi (72 x 72): column sums {sorted(set(int(sum(PHI[:, j])) for j in range(72)))}; row-sum histogram {dict(collections.Counter(int(sum(PHI[i, :])) for i in range(72)))}")
lam = symbols('lambda'); cp = factor(PHI.charpoly(lam).as_expr())
say(f" charpoly(Phi) = {cp}")
ns = (PHI - 8 * eye(72)).nullspace()
say(f" nullity of Phi - 8: {len(ns)} (simple eigenvalue 8: {len(ns) == 1})")
u1 = ns[0]; u1 = u1 / sum(u1); u1 = [Fraction(int(x.p), int(x.q)) for x in u1]
say(f" u_1 >= 0: {all(x >= 0 for x in u1)}; sum {sum(u1)}; max denominator {max(x.denominator for x in u1)}; number of distinct values {len(set(u1))}; min {min(u1)}, max {max(u1)}")
# surface-corrected convergence: compare census fractions of T_5 and T_6 with u_1
for m in (5, 6):
    G, T = gen_poses(m); grid = owner_grid(2 ** (m + 1), G, T); cm = star_census(G, T, grid, L1ODD); tot = sum(cm.values())
    dev = max(abs(cm.get(k, 0) / tot - float(u1[I1[k]])) for k in V1)
    say(f"   T_{m}: complete 1-stars {tot}; max |census fraction - u_1| = {dev:.2e}  (surface corrections O(2^-m))")
    del G, T, grid
# per-tile observables from the 1-star type: 48 inter-tile edges touching the center
def center_edges(poses, own, center):
    cs = [tuple(int(x) for x in c) for c in cubes_of_poses(poses[center][0][None], poses[center][1][None])[0]]; seen = set(); out = []
    for c in cs:
        for kax in range(3):
            i, j = [x for x in range(3) if x != kax]
            for di, dj in itertools.product((0, 1), repeat=2):
                p = list(c); p[i] += di; p[j] += dj; p = tuple(p)
                if (kax, p) in seen: continue
                seen.add((kax, p)); cyc = []
                for a, b in [(0, 0), (1, 0), (1, 1), (0, 1)]:
                    q = list(p); q[i] -= a; q[j] -= b; cyc.append(tuple(q))
                out.append(cyc)
    return out
nminus = collections.defaultdict(Fraction); classw = {c: Fraction(0) for c in CLASSES}; nnonflat = collections.defaultdict(Fraction)
for k in V1:
    poses, center = poses_from_key(k); own = owner_dict(poses); fid = [gidx[key(g)] for g, t in poses]
    nm = 0; nnf = 0
    for cyc in center_edges(poses, own, center):
        tl = [own[q] for q in cyc]
        if len(set(tl)) == 1: continue
        W = np.eye(2, dtype=complex)
        for s in range(4):
            t1, t2 = tl[s], tl[(s + 1) % 4]
            if t1 == t2: continue
            d = np.array(cyc[(s + 1) % 4]) - np.array(cyc[s]); W = W @ LINK[fid[t1], fid[t2], int(np.nonzero(d)[0][0])]
        cl = CLASS[q8label(W)]
        nm += (cl == '-1'); nnf += (cl != '1'); classw[cl] += u1[I1[k]] / len(set(tl))
    nminus[nm] += u1[I1[k]]; nnonflat[nnf] += u1[I1[k]]
say(f" plaquette classes recovered from u_1 (each plaquette weighted 1/#tiles around it), per tile: " + ", ".join(f"{c}: {classw[c]}" for c in CLASSES) + f"; total {sum(classw.values())}")
say(f"   equals 18 x Theorem A frequencies (19/2, 13/8, 2, 23/8, 2): {[classw[c] for c in CLASSES] == [F(19,2), F(13,8), F(2), F(23,8), F(2)]}")
say(f" per-tile distribution of the number of class -1 plaquettes among the 48 inter-tile plaquettes touching a tile (exact):")
for n in sorted(nminus): say(f"     {n:3d}: {str(nminus[n]):>18s} = {float(nminus[n]):.6f}")
say(f"   mean {sum(n*v for n, v in nminus.items())} = {float(sum(n*v for n, v in nminus.items())):.6f}")
say(f" per-tile distribution of the number of NON-FLAT plaquettes among the 48: " + ", ".join(f"{n}: {float(nnonflat[n]):.5f}" for n in sorted(nnonflat)))
# 2-star frequencies
PHI2 = {k: Phi_r(k, L2ODD) for k in V1}; V2 = sorted({kk for k in V1 for kk in PHI2[k]}, key=lambda k: sorted(k)); I2 = {k: i for i, k in enumerate(V2)}
u2 = [Fraction(0)] * len(V2)
for k in V1:
    for kk in PHI2[k]: u2[I2[kk]] += u1[I1[k]] / 8
say(f" 2-star types: {len(V2)}; u_2 = Phi_2 u_1 / 8: sum {sum(u2)}, min {min(u2)} = {float(min(u2)):.3e}, max {max(u2)} = {float(max(u2)):.4f}, max denominator {max(x.denominator for x in u2)}")
G6, T6 = gen_poses(6); grid6 = owner_grid(128, G6, T6); c2_6 = star_census(G6, T6, grid6, L2ODD); tot = sum(c2_6.values())
say(f"   T_6: complete 2-stars {tot}, max |census fraction - u_2| = {max(abs(c2_6.get(k, 0)/tot - float(u2[I2[k]])) for k in V2):.2e}")
del G6, T6, grid6
with open(os.path.join(HERE, 'results', 'phase5b_e_star_frequencies.txt'), 'w') as f:
    f.write("# exact limit frequencies of the 72 legal 1-star types (relative poses (frame index in Gs, dx, dy, dz) of the members)\n")
    for k in V1: f.write(f"{u1[I1[k]]}\t{[decode(c) for c in sorted(k)]}\n")
    f.write("# exact limit frequencies of the 165 legal 2-star types\n")
    for k in V2: f.write(f"{u2[I2[k]]}\t{[decode(c) for c in sorted(k)]}\n")
say(f" saved audit/results/phase5b_e_star_frequencies.txt;  wall time Part B {time.time()-t0:.0f}s; total {time.time()-T_START:.0f}s, rss {rss():.2f} GB")
