"""
Phase 5a / Task D2: ADVERSARIAL VERIFICATION OF THE B2a PERIODIC-CONTROL CENSUS.

Everything below (crystal, owner map, cosets, Bloch matrices, band minimiser, torus plaquette flux) is written
independently of audit/phase5a_periodic_control.py.  Only the Q8 link primitives (SIG, perm_mat, FR30, U3,
clifford_link, q8label) are imported from audit/independent_clifford_q8_audit.py, and clifford_link/q8label are used
solely to CROSS-CHECK the integer Q8 tables built here.  The B2a conventions that are reproduced here are those needed
to PARSE its JSONL records (SO3Z enumeration order, coset key/order) -- the physics is recomputed.

Run from the repository root:
  OMP_NUM_THREADS=1 python3 -u -I audit/phase5a_d2_census_verify.py [stage ...]
stages: crystal records search regress bijections   (default: all)
Output: audit/results/phase5a_d2_census_verify.txt (stdout is also written there).
"""
import os, sys, time, json, glob, itertools, collections
for _v in ('OPENBLAS_NUM_THREADS', 'OMP_NUM_THREADS', 'MKL_NUM_THREADS'): os.environ.setdefault(_v, '1')
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import numpy as np
import scipy.optimize as sopt
from independent_clifford_q8_audit import FR30, U3, perm_mat, clifford_link, q8label, SIG

OUT = os.path.join(HERE, 'results', 'phase5a_d2_census_verify.txt')
T0 = time.time()
_fh = None
def log(*a):
    s = " ".join(str(x) for x in a)
    print(s, flush=True)
    if _fh is not None: _fh.write(s + "\n"); _fh.flush()

# =====================================================================================================================
# 1. Chair crystal on Lambda_7 (own derivation)
# =====================================================================================================================
U3S = set(U3)                                              # the 7 cubes of the chair at the origin (lower corners)
BL = np.array([[1, 1, 1], [2, 1, -1], [-1, 2, 1]], dtype=int)   # rows: lattice basis (ambient coordinates), as in B2a
BLinvT = np.linalg.inv(BL.T.astype(float))
def phi(c): return (int(c[0]) + 2 * int(c[1]) + 4 * int(c[2])) % 7
RES2U = {}
for u in U3:
    assert phi(u) not in RES2U; RES2U[phi(u)] = np.array(u, dtype=int)
assert sorted(RES2U) == list(range(7))                     # phi restricted to U3 is a bijection onto Z_7 (0 <- (0,0,0))
def owner(c):
    """Lattice point (ambient) of the chair containing unit cube c.  Unique because the chairs x+U3 (x in ker phi) cover
    each residue class of phi exactly once: c in x+U3  <=>  c-x in U3 and phi(c-x)=phi(c)  <=>  c-x = RES2U[phi(c)]."""
    c = np.asarray(c, dtype=int); return c - RES2U[phi(c)]
def to_L(x):
    """ambient lattice point -> integer coordinates in the basis BL (x = m @ BL)."""
    m = BLinvT @ np.asarray(x, dtype=float); mi = np.rint(m).astype(int)
    assert np.allclose(m, mi, atol=1e-9) and (mi @ BL == np.asarray(x)).all(), x
    return mi
def from_L(m): return np.asarray(m, dtype=int) @ BL

def chair_panels():
    """Boundary unit panels of the chair at the origin: (d_ambient to neighbour chair, outward normal n, cube u)."""
    out = []
    for u in U3:
        for ax in range(3):
            for s in (1, -1):
                w = np.array(u, dtype=int); w[ax] += s
                if tuple(w) in U3S: continue
                out.append((owner(w), np.eye(3, dtype=int)[ax] * s, np.array(u)))
    return out
PANELS = chair_panels()
PANELS_M = [to_L(d) for d, n, u in PANELS]

def stage_crystal():
    log("=" * 110); log("1. LAMBDA_7 CHAIR CRYSTAL -- own re-derivation of claim (a)")
    log(f" basis rows {BL.tolist()}, det={round(np.linalg.det(BL))}, phi(rows)={[phi(b) for b in BL]} (all 0: rows lie in ker phi); "
        f"index of ker phi in Z^3 = 7 = |det|, so rows span ker phi iff det=+-7: {abs(round(np.linalg.det(BL)))==7}")
    log(f" phi on U3: {[(u, phi(u)) for u in U3]} -> bijection onto Z_7: True (asserted at import)")
    # exact tiling check on a torus Z^3/(7 Z)^3 ... simpler: a box, with all chairs that meet it
    N = 14; box = list(itertools.product(range(N), repeat=3))
    cover = collections.Counter()
    pts = {tuple(np.array(c) - np.array(u)) for c in box for u in U3}
    pts = [x for x in pts if phi(x) == 0]
    for x in pts:
        for u in U3:
            c = (x[0] + u[0], x[1] + u[1], x[2] + u[2])
            if 0 <= c[0] < N and 0 <= c[1] < N and 0 <= c[2] < N: cover[c] += 1
    inbox = [cover[c] for c in box]
    log(f" direct cover count on {N}^3 box by all ker(phi)-translates of the chair meeting it: once={sum(v==1 for v in inbox)}, "
        f"zero={sum(v==0 for v in inbox)}, >1={sum(v>1 for v in inbox)}  (exact tiling <=> {N**3},0,0)")
    ok = all(tuple(np.array(c) - owner(c)) in U3S and phi(owner(c)) == 0 for c in box)
    log(f" owner map: owner(c) in ker phi and c - owner(c) in U3 for all box cubes: {ok}")
    # panels
    cnt = collections.Counter(tuple(int(x) for x in d) for d, n, u in PANELS)
    log(f" chair: 7 cubes x 6 faces = 42 face slots; internal adjacencies = {sum(1 for u in U3 for ax in range(3) if tuple(np.array(u)+np.eye(3,dtype=int)[ax]) in U3S)} (x2 slots)"
        f"; boundary panels = {len(PANELS)}; distinct neighbour chairs = {len(cnt)}")
    for d, m in sorted(cnt.items()):
        nn = collections.Counter(tuple(int(x) for x in n) for dd, n, u in PANELS if tuple(int(x) for x in dd) == d)
        log(f"    d={d}  L-coords={to_L(d).tolist()}  panels={m}  normals={dict(nn)}  |d|^2={sum(x*x for x in d)}")
    log(f" multiplicity symmetric under d->-d: {all(cnt[tuple(-np.array(d))]==m for d,m in cnt.items())};  sum={sum(cnt.values())}")
    # inter-tile plaquettes per chair: count lattice edges of Z^3 (indexed by the cube at their lower corner in the
    # transverse plane) whose 4 surrounding cubes are not all in one chair; average over a large box
    N = 21; tot = 0; internal = 0
    for c in itertools.product(range(N), repeat=3):
        c = np.array(c)
        for (i, j) in ((0, 1), (1, 2), (0, 2)):
            ei = np.eye(3, dtype=int)[i]; ej = np.eye(3, dtype=int)[j]
            ows = {tuple(owner(c + s)) for s in (0 * ei, ei, ei + ej, ej)}
            tot += 1; internal += (len(ows) == 1)
    log(f" lattice edges in {N}^3 box (3 per cube): {tot} = 21 per chair; internal to one chair: {internal} = {internal/(N**3/7):.4f} per chair; "
        f"inter-tile: {(tot-internal)/(N**3/7):.4f} per chair (claim: 18)")
    # independent count: each cube of a chair has 3 edges 'owned'; an edge is internal iff its 4 cubes are in the chair
    intr = sum(1 for u in U3 for (i, j) in ((0, 1), (1, 2), (0, 2)) if all(tuple(np.array(u)+s) in U3S for s in (np.eye(3,dtype=int)[i], np.eye(3,dtype=int)[i]+np.eye(3,dtype=int)[j], np.eye(3,dtype=int)[j])))
    log(f" chair-intrinsic count of internal lattice edges (all 4 cubes in the chair): {intr} -> inter-tile plaquettes per chair = 21 - {intr} = {21-intr}")

# =====================================================================================================================
# 2. SO(3,Z), Q8 integer tables
# =====================================================================================================================
# B2a enumeration order (needed ONLY to decode the 'frames' field of its records)
SO3Z = [np.diag(s) @ perm_mat(p) for p in itertools.permutations(range(3)) for s in itertools.product((1, -1), repeat=3)]
SO3Z = [g for g in SO3Z if round(np.linalg.det(g)) == 1]
assert len(SO3Z) == 24 and len({tuple(g.flatten()) for g in SO3Z}) == 24
SO3Z_IDX = {tuple(g.flatten()): i for i, g in enumerate(SO3Z)}
I3 = np.eye(3, dtype=int)
FR30_FRAMES = [perm_mat(FR30['0'])] + [np.diag([1 - 2 * v[0], 1 - 2 * v[1], 1 - 2 * v[2]]) @ perm_mat(FR30[v]) for v in U3]
FR30_LABELS = ['centre'] + [str(v) for v in U3]
FR30_IDX = [SO3Z_IDX[tuple(f.flatten())] for f in FR30_FRAMES]

# Q8 as integers: element e <-> matrix Q8M[e]; 0:+1 1:-1 2:+i*sx 3:-i*sx 4:+i*sy 5:-i*sy 6:+i*sz 7:-i*sz
Q8M = [np.eye(2, dtype=complex), -np.eye(2, dtype=complex)]
for k in range(3): Q8M += [1j * SIG[k], -1j * SIG[k]]
Q8CLASS = np.array([0, 1, 2, 2, 2, 2, 2, 2])             # 0: +1, 1: -1, 2: traceless
def q8_of(U):
    for e, M in enumerate(Q8M):
        if np.allclose(U, M, atol=1e-9): return e
    raise ValueError("not in Q8")
Q8MUL = np.array([[q8_of(Q8M[a] @ Q8M[b]) for b in range(8)] for a in range(8)], dtype=int)
Q8INV = np.array([q8_of(Q8M[a].conj().T) for a in range(8)], dtype=int)
NORMALS = [tuple(s * I3[ax]) for ax in range(3) for s in (1, -1)]
NIDX = {n: i for i, n in enumerate(NORMALS)}
def sdot_(u): return sum(int(u[j]) * SIG[j] for j in range(3))
# LINK[g_a, g_b, n] = Q8 element of (sigma . M_a^T n)(sigma . M_b^T n), own formula
LINK = np.zeros((24, 24, 6), dtype=int)
for a, Ma in enumerate(SO3Z):
    for b, Mb in enumerate(SO3Z):
        for ni, n in enumerate(NORMALS):
            nn = np.array(n)
            LINK[a, b, ni] = q8_of(sdot_(Ma.T @ nn) @ sdot_(Mb.T @ nn))
LINKM = np.array([Q8M[e] for e in range(8)])              # (8,2,2)

def q8_tables_check(rng):
    log("=" * 110); log("2. Q8 TABLES vs the audited primitive clifford_link (cross-check only)")
    bad = 0
    for t in range(2000):
        a, b = rng.integers(0, 24, 2); ni = rng.integers(0, 6)
        C = clifford_link(SO3Z[a], SO3Z[b], np.array(NORMALS[ni]))
        bad += not np.allclose(C, Q8M[LINK[a, b, ni]])
    rev = all(LINK[b, a, ni] == Q8INV[LINK[a, b, ni]] for a in range(24) for b in range(24) for ni in range(6))
    revn = all(LINK[a, b, ni ^ 1] == LINK[a, b, ni] for a in range(24) for b in range(24) for ni in range(6))
    cls = all(q8label(Q8M[e]) in {0: ['+1'], 1: ['-1'], 2: ['+i', '-i', '+j', '-j', '+k', '-k']}[Q8CLASS[e]] for e in range(8))
    log(f" 2000 random (M_a,M_b,n): own table == clifford_link: mismatches={bad};  C_ba == C_ab^dagger for all 24x24x6: {rev};  "
        f"C independent of the sign of n: {revn};  class labels agree with q8label: {cls};  Q8 closed under product: {set(Q8MUL.flatten())==set(range(8))}")
    log(f" FR30 level-1 frames (SO3Z indices): {dict(zip(FR30_LABELS, FR30_IDX))}")

# =====================================================================================================================
# 3. Sublattices, cosets, hop structure, torus plaquettes (own code)
# =====================================================================================================================
def hnf_list(k):
    out = []
    for d1 in [d for d in range(1, k + 1) if k % d == 0]:
        for d2 in [d for d in range(1, k // d1 + 1) if (k // d1) % d == 0]:
            d3 = k // (d1 * d2)
            for a in range(d2):
                for b in range(d3):
                    for c in range(d3):
                        out.append(np.array([[d1, a, b], [0, d2, c], [0, 0, d3]], dtype=int))
    return out

class Crystal:
    """Sublattice L' of L=Z^3 (L-coordinates) given by an upper-triangular HNF row basis S (det k).  Cosets are
    indexed by the canonical representative m in [0,d1)x[0,d2)x[0,d3) obtained by row reduction, and then ORDERED by
    the B2a key tuple((k S^{-1})^T m mod k) sorted, so that the 'frames' lists in B2a's records can be decoded."""
    def __init__(self, S):
        S = np.asarray(S, dtype=int); assert S.shape == (3, 3) and S[1, 0] == 0 and S[2, 0] == 0 and S[2, 1] == 0 and (np.diag(S) > 0).all()
        self.S = S; self.k = int(S[0, 0] * S[1, 1] * S[2, 2])
        self.adjT = np.rint(self.k * np.linalg.inv(S.astype(float))).astype(int).T
        assert (self.adjT @ S.T == self.k * I3).all()
        reps = [np.array(m) for m in itertools.product(range(S[0, 0]), range(S[1, 1]), range(S[2, 2]))]
        assert len(reps) == self.k
        keyed = sorted((tuple((self.adjT @ m) % self.k), m) for m in reps)
        assert len({kk for kk, _ in keyed}) == self.k, "B2a key not injective on canonical reps (should never happen)"
        self.reps = [m for _, m in keyed]
        self.rep_index = {tuple(m): i for i, m in enumerate(self.reps)}
        self.Bp = S @ BL                                              # rows: L' basis in ambient coordinates
        self.BpinvT = np.linalg.inv(self.Bp.T.astype(float))
        # hops: (coset a, coset b, ambient displacement d, normal index)
        hops = []
        for a, m in enumerate(self.reps):
            for (d, n, u), md in zip(PANELS, PANELS_M):
                hops.append((a, self.coset(m + md), d, NIDX[tuple(n)]))
        self.hops = hops
        self.D = np.array([h[2] for h in hops], dtype=float)         # (F,3)
        self.hA = np.array([h[0] for h in hops]); self.hB = np.array([h[1] for h in hops]); self.hN = np.array([h[3] for h in hops])
        self._plaquettes()
    def reduce(self, m):
        m = np.array(m, dtype=int); S = self.S
        for i in (0, 1, 2):
            t = m[i] // S[i, i]; m = m - t * S[i]
        assert (m >= 0).all() and (m < np.diag(S)).all()
        return m
    def coset(self, m): return self.rep_index[tuple(self.reduce(m))]
    def coset_of_cube(self, c): return self.coset(to_L(owner(c)))
    def _plaquettes(self):
        """All lattice edges of the torus Z^3/L': one fundamental domain = the 7k cubes of the k representative chairs;
        each cube owns the 3 edges at its corner (1,1,*),(1,*,1),(*,1,1)... i.e. the ring c, c+ei, c+ei+ej, c+ej.
        For each ring store the 4 cosets and the 4 normals between consecutive cubes (ring order), plus a mask for
        'same chair' steps (identity link)."""
        rings_c = []; rings_n = []; same = []; internal = 0
        for m in self.reps:
            x = from_L(m)
            for u in U3:
                c = x + np.array(u)
                for (i, j) in ((0, 1), (1, 2), (0, 2)):
                    ei = I3[i]; ej = I3[j]
                    ring = [c, c + ei, c + ei + ej, c + ej]
                    own = [owner(cc) for cc in ring]
                    if len({tuple(o) for o in own}) == 1: internal += 1; continue
                    cos = [self.coset(to_L(o)) for o in own]
                    ns = []; sm = []
                    for t in range(4):
                        n = ring[(t + 1) % 4] - ring[t]
                        ns.append(NIDX[tuple(n)]); sm.append((own[t] == own[(t + 1) % 4]).all())
                    rings_c.append(cos); rings_n.append(ns); same.append(sm)
        self.n_internal = internal; self.n_inter = len(rings_c)
        assert internal + self.n_inter == 21 * self.k
        self.PC = np.array(rings_c, dtype=int); self.PN = np.array(rings_n, dtype=int); self.PS = np.array(same, dtype=bool)
    # ---------- flux ----------
    def flux_counts(self, frames):
        """frames: array of k SO3Z indices. Returns (n_plus1, n_minus1, n_traceless) over inter-tile plaquettes."""
        fr = np.asarray(frames, dtype=int)
        W = np.zeros(self.n_inter, dtype=int)                             # start with +1
        for t in range(4):
            e = LINK[fr[self.PC[:, t]], fr[self.PC[:, (t + 1) % 4]], self.PN[:, t]]
            e = np.where(self.PS[:, t], 0, e)                              # same chair: identity
            W = Q8MUL[W, e]
        cl = Q8CLASS[W]
        return int(np.sum(cl == 0)), int(np.sum(cl == 1)), int(np.sum(cl == 2))
    def flux_fractions(self, frames):
        p1, m1, tr = self.flux_counts(frames); n = self.n_inter
        return 1 - p1 / n, tr / n, m1 / n
    # ---------- Bloch ----------
    def bloch_blocks(self, frames):
        fr = np.asarray(frames, dtype=int); k = self.k
        C = LINKM[LINK[fr[self.hA], fr[self.hB], self.hN]]              # (F,2,2)
        E = np.zeros((len(self.hops), 2 * k, 2 * k), dtype=complex)
        for f in range(len(self.hops)):
            a, b = self.hA[f], self.hB[f]
            E[f, 2 * a:2 * a + 2, 2 * b:2 * b + 2] += C[f]
        return E.reshape(len(self.hops), -1)
    def Hq(self, E, q):
        ph = np.exp(1j * (self.D @ q)); k = self.k
        return 24.0 * np.eye(2 * k) - (ph @ E).reshape(2 * k, 2 * k)
    def Hq_batch(self, E, Q):
        ph = np.exp(1j * (Q @ self.D.T)); k = self.k
        return 24.0 * np.eye(2 * k)[None] - (ph @ E).reshape(len(Q), 2 * k, 2 * k)
    def q_of_theta(self, th):
        # Bloch phases e^{i q.x} are L'-periodic in q modulo 2pi L'^*: q = 2 pi Bp^{-1} theta  (Bp q = 2 pi theta)
        return 2 * np.pi * np.linalg.solve(self.Bp.astype(float), np.asarray(th, dtype=float))
    def theta_of_q(self, q): return (self.Bp @ np.asarray(q) / (2 * np.pi)) % 1.0
    def band_bottom(self, frames, ngrid=8, nstart=3, refine=True):
        E = self.bloch_blocks(frames)
        th = np.array(list(itertools.product(np.arange(ngrid) / ngrid, repeat=3)))
        Q = (2 * np.pi * np.linalg.solve(self.Bp.astype(float), th.T)).T
        w = np.linalg.eigvalsh(self.Hq_batch(E, Q))
        e0 = w[:, 0]; order = np.argsort(e0)
        best = (float(e0[order[0]]), Q[order[0]])
        if refine:
            f = lambda q: np.linalg.eigvalsh(self.Hq(E, q))[0]
            for s in order[:nstart]:
                r = sopt.minimize(f, Q[s], method='Nelder-Mead', options=dict(xatol=1e-9, fatol=1e-13, maxiter=4000, initial_simplex=Q[s] + 0.15 * np.r_[np.zeros((1, 3)), np.eye(3)]))
                r2 = sopt.minimize(f, r.x, method='BFGS', options=dict(gtol=1e-10))
                for cand in (r.fun, r.x), (r2.fun, r2.x):
                    if cand[0] < best[0] - 1e-14: best = (float(cand[0]), np.array(cand[1]))
        herm = np.abs(self.Hq(E, best[1]) - self.Hq(E, best[1]).conj().T).max()
        assert herm < 1e-10
        return dict(E=best[0], q=best[1], theta=self.theta_of_q(best[1]), grid_min=float(e0.min()))

CRYSTALS = {}
def crystal(S):
    key = tuple(map(tuple, np.asarray(S, dtype=int)))
    if key not in CRYSTALS: CRYSTALS[key] = Crystal(np.array(key))
    return CRYSTALS[key]

FR30_F = dict(nontriv=17 / 36, traceless=55 / 144, minus1=13 / 144)
TOL = (0.03, 0.04, 0.04)
def flux_matched(fn, ft, fm): return abs(fn - FR30_F['nontriv']) < TOL[0] and abs(ft - FR30_F['traceless']) < TOL[1] and abs(fm - FR30_F['minus1']) < TOL[2]

def crystal_torus_checks():
    log("=" * 110); log("3. TORUS STRUCTURE CHECKS (own coset / plaquette code)")
    for S in (I3, np.diag([1, 1, 2]), np.diag([2, 2, 1]), np.array([[1, 0, 2], [0, 1, 2], [0, 0, 4]]), 2 * I3, np.array([[1, 0, 4], [0, 1, 5], [0, 0, 8]])):
        cr = crystal(S)
        hopcount = collections.Counter(cr.hA.tolist())
        log(f" S={S.tolist()} k={cr.k}: cosets={len(cr.reps)} reps={[m.tolist() for m in cr.reps]}; hops={len(cr.hops)} (={24*cr.k}: {all(v==24 for v in hopcount.values())}); "
            f"lattice edges={21*cr.k}, internal={cr.n_internal} (=3k: {cr.n_internal==3*cr.k}), inter-tile={cr.n_inter} (=18k: {cr.n_inter==18*cr.k})")
    log(f" number of HNF sublattices: index 2: {len(hnf_list(2))}, index 4: {len(hnf_list(4))}, index 8: {len(hnf_list(8))}  (formula sum_{{d|n}} d*sigma(d): 7, 35, 155)")
    # trivial decoration: all links +1, H(q) = 24 - sum_f e^{iq.d_f}: E(Gamma)=0
    cr = crystal(I3); r = cr.band_bottom([0])
    log(f" k=1 all frames I: E_per={r['E']:.12f} at theta={np.round(r['theta'],6).tolist()}; flux fractions={cr.flux_fractions([0])}")

# =====================================================================================================================
# 4. Records
# =====================================================================================================================
def load_records():
    out = []
    for fn in sorted(glob.glob(os.path.join(HERE, 'results', 'phase5a_periodic_control_records*.jsonl'))):
        with open(fn) as f:
            for l in f:
                if l.strip(): out.append(json.loads(l))
    return out
def dedupe(recs):
    seen = set(); u = []
    for r in recs:
        key = (tuple(map(tuple, r['S'])), tuple(r['frames']))
        if key in seen: continue
        seen.add(key); u.append(r)
    return u

def stage_records(rng, n2=60, n4=160, n8=100):
    log("=" * 110); log("4. RECOMPUTATION OF A RANDOM SAMPLE OF B2a RECORDS (own Bloch solver: 8^3 grid + Nelder-Mead/BFGS refinement from 3 best grid points; own torus flux)")
    allr = load_records(); uniq = dedupe(allr)
    ks = collections.Counter(r['k'] for r in uniq)
    log(f" records loaded: {len(allr)} lines, {len(uniq)} distinct (S, frames) decorations: {dict(sorted(ks.items()))}   (claim (b): 44539)")
    Es = np.array([r['E'] for r in uniq])
    log(f" claim (b) from records: E_per min={Es.min():.6f} max={Es.max():.6f}; fraction > 8.770: {np.mean(Es > 8.770):.4f}; fraction >= 8.770: {np.mean(Es >= 8.770):.4f}")
    must = ["k=4 S=[[1, 0, 2], [0, 1, 2], [0, 0, 4]] tri=(18, 2, 10)", "k=4 S=[[1, 1, 1], [0, 2, 1], [0, 0, 2]] tri=(15, 20, 15)",
            "k=8 S=[[1, 0, 4], [0, 1, 5], [0, 0, 8]] random#1", "k=4 S=[[1, 1, 0], [0, 2, 1], [0, 0, 2]] tri=(23, 23, 14)",
            "k=8 2L FR30 natural bijection [1, 2, 3, 4, 5, 6, 7, 0]", "k=1 frame=[[1, 0, 0], [0, 1, 0], [0, 0, 1]]"]
    sample = []
    for lab in must:
        m = [r for r in uniq if r['label'] == lab]; assert len(m) == 1, lab; sample.append(m[0])
    for k, n in ((2, n2), (4, n4), (8, n8)):
        pool = [r for r in uniq if r['k'] == k]
        idx = rng.choice(len(pool), size=min(n, len(pool)), replace=False)
        sample += [pool[i] for i in idx]
    log(f" sample size: {len(sample)} ({len(must)} mandatory + k=2:{n2}, k=4:{n4}, k=8:{n8} random)")
    t = time.time(); rows = []
    for r in sample:
        cr = crystal(np.array(r['S'])); fr = np.array(r['frames'])
        assert len(fr) == cr.k
        bb = cr.band_bottom(fr); fn, ft, fm = cr.flux_fractions(fr)
        p1, m1, tr = cr.flux_counts(fr)
        rec_cls = r['cls']; rec_tr = rec_cls['i'] + rec_cls['j'] + rec_cls['k']
        rows.append(dict(label=r['label'], k=r['k'], E_rec=r['E'], E_mine=bb['E'], dE=bb['E'] - r['E'], dfn=fn - r['f_nontriv'], dft=ft - r['f_traceless'], dfm=fm - r['f_minus1'],
                         cnt_match=(p1 == rec_cls['1'] and m1 == rec_cls['-1'] and tr == rec_tr and cr.n_inter == r['inter']), grid_min=bb['grid_min'], theta=bb['theta']))
    dt = time.time() - t
    dE = np.array([x['dE'] for x in rows]); adE = np.abs(dE)
    log(f" wall time {dt:.1f}s for {len(rows)} decorations")
    log(f" E_per discrepancy (mine - record): max|dE|={adE.max():.3e}, median|dE|={np.median(adE):.1e}; #|dE|>1e-6: {int(np.sum(adE>1e-6))}; #|dE|>1e-3: {int(np.sum(adE>1e-3))}; "
        f"most negative dE (mine lower = record missed a lower point): {dE.min():.3e}; most positive dE (mine higher = my minimiser worse): {dE.max():.3e}")
    for k in (1, 2, 4, 8):
        sel = [x for x in rows if x['k'] == k]
        if sel: log(f"   k={k}: n={len(sel)} max|dE|={max(abs(x['dE']) for x in sel):.3e}")
    log(f" flux-fraction discrepancy: max|d f_nontriv|={max(abs(x['dfn']) for x in rows):.1e}, max|d f_traceless|={max(abs(x['dft']) for x in rows):.1e}, max|d f_-1|={max(abs(x['dfm']) for x in rows):.1e};"
        f" exact class-count agreement (+1,-1,traceless,inter): {sum(x['cnt_match'] for x in rows)}/{len(rows)}")
    log(" mandatory decorations:")
    for x in rows[:len(must)]:
        log(f"   {x['label'][:62]:62s} E_rec={x['E_rec']:.9f} E_mine={x['E_mine']:.9f} dE={x['dE']:+.2e} theta_mine={np.round(x['theta'],4).tolist()} grid8_min={x['grid_min']:.6f}")
    worst = sorted(rows, key=lambda x: -abs(x['dE']))[:5]
    log(" five largest |dE|:")
    for x in worst: log(f"   {x['label'][:62]:62s} E_rec={x['E_rec']:.9f} E_mine={x['E_mine']:.9f} dE={x['dE']:+.3e}")
    # claim (c) from records with my matching criterion
    mt = [r for r in uniq if flux_matched(r['f_nontriv'], r['f_traceless'], r['f_minus1'])]
    Em = np.array([r['E'] for r in mt])
    log(f" claim (c) from records (own filter, strict <): n={len(mt)}, E_per min={Em.min():.4f} median={np.median(Em):.4f} max={Em.max():.4f}; top-4 labels: {[r['label'][:55] for r in sorted(mt, key=lambda r: -r['E'])[:4]]}")
    return rows

# =====================================================================================================================
# 5. Counterexample search
# =====================================================================================================================
def stage_search(rng, n_flux=60000, n_bloch_uniform=3000, hill_steps=200, ngrid_search=8):
    log("=" * 110); log("5. COUNTEREXAMPLE SEARCH: random decorations on ALL index-4 and index-8 HNF sublattices (own code)")
    subs = [(4, S) for S in hnf_list(4)] + [(8, S) for S in hnf_list(8)]
    log(f" {len(subs)} sublattices; frames: coset 0 fixed to I (global right factor is a unitary conjugation of H), others uniform in SO(3,Z)")
    t = time.time(); matched = []; uniform = []
    for i in range(n_flux):
        k, S = subs[rng.integers(len(subs))]; cr = crystal(S)
        fr = np.r_[0, rng.integers(0, 24, k - 1)]
        fn, ft, fm = cr.flux_fractions(fr)
        if flux_matched(fn, ft, fm): matched.append((S, fr, fn, ft, fm))
        if i < n_bloch_uniform: uniform.append((S, fr, fn, ft, fm))
    log(f" flux computed for {n_flux} random decorations in {time.time()-t:.1f}s: flux-matched (|dfn|<0.03,|dft|<0.04,|dfm|<0.04): {len(matched)} ({len(matched)/n_flux:.4f})")
    # Bloch on all matched + first n_bloch_uniform
    t = time.time(); res_u = []
    for (S, fr, fn, ft, fm) in uniform:
        res_u.append((crystal(S).band_bottom(fr, ngrid=ngrid_search)['E'], S, fr, fn, ft, fm))
    Eu = np.array([r[0] for r in res_u])
    log(f" Bloch band bottom for {len(res_u)} uniform random decorations ({time.time()-t:.1f}s): E_per min={Eu.min():.6f} max={Eu.max():.6f} mean={Eu.mean():.4f}; fraction >8.770: {np.mean(Eu>8.770):.4f}")
    mu = [r for r in res_u if flux_matched(r[3], r[4], r[5])]
    if mu: log(f"   of which flux-matched: {len(mu)}, E_per max={max(r[0] for r in mu):.6f}")
    t = time.time(); res_m = []
    for (S, fr, fn, ft, fm) in matched:
        res_m.append((crystal(S).band_bottom(fr, ngrid=ngrid_search)['E'], S, fr, fn, ft, fm))
    Em = np.array([r[0] for r in res_m])
    log(f" Bloch band bottom for ALL {len(res_m)} flux-matched decorations ({time.time()-t:.1f}s): E_per min={Em.min():.6f} median={np.median(Em):.6f} max={Em.max():.6f}")
    log(f"   number of flux-matched with E_per > 8.770: {int(np.sum(Em>8.770))};  > 8.5: {int(np.sum(Em>8.5))};  > 8.18: {int(np.sum(Em>8.18))};  > 8.1772: {int(np.sum(Em>8.1772))}")
    top = sorted(res_m, key=lambda r: -r[0])[:5]
    log(" top-5 flux-matched random decorations:")
    for E, S, fr, fn, ft, fm in top:
        log(f"   E_per={E:.6f} k={len(fr)} S={S.tolist()} frames={fr.tolist()} flux nontriv={fn:.4f} traceless={ft:.4f} -1={fm:.4f}")
    # Hill climb from the best flux-matched decoration (all single-coset frame changes), constraint: stay flux-matched
    best_E, S, fr, fn, ft, fm = top[0]; cr = crystal(S); k = cr.k
    log(f" HILL-CLIMB (greedy best-improvement over all single-coset frame changes, flux-match constraint, {hill_steps} steps max, random "
        f"constrained kick when stuck) from E_per={best_E:.6f} on S={S.tolist()}")
    t = time.time(); cur = fr.copy(); curE = best_E; glob_best = (curE, cur.copy()); stuck = 0; nbloch = 0; nkick = 0
    for step in range(hill_steps):
        cands = []
        for c in range(k):
            for g in range(24):
                if g == cur[c]: continue
                fr2 = cur.copy(); fr2[c] = g
                if flux_matched(*cr.flux_fractions(fr2)): cands.append(fr2)
        Ec = []
        for fr2 in cands:
            Ec.append(cr.band_bottom(fr2, ngrid=4, nstart=2)['E']); nbloch += 1
        if cands and max(Ec) > curE + 1e-9:
            j = int(np.argmax(Ec)); cur = cands[j]; curE = cr.band_bottom(cur, ngrid=ngrid_search)['E']; stuck = 0
        else:
            stuck += 1; nkick += 1
            # random kick: change two cosets at random subject to the constraint (sideways/downhill move)
            for _ in range(200):
                fr2 = cur.copy(); cc = rng.choice(k, size=2, replace=False); fr2[cc] = rng.integers(0, 24, 2)
                if flux_matched(*cr.flux_fractions(fr2)): cur = fr2; curE = cr.band_bottom(cur, ngrid=ngrid_search)['E']; break
        if curE > glob_best[0]: glob_best = (curE, cur.copy())
        if step % 25 == 0 or step == hill_steps - 1:
            log(f"   step {step:3d}: current E={curE:.6f} best E={glob_best[0]:.6f} (#constrained neighbours {len(cands)}, kicks so far {nkick})")
    Eb = cr.band_bottom(glob_best[1], ngrid=12)['E']
    fnb, ftb, fmb = cr.flux_fractions(glob_best[1])
    log(f" hill-climb done in {time.time()-t:.1f}s ({nbloch} coarse Bloch evaluations): best flux-matched E_per={glob_best[0]:.6f} (12^3-grid recheck {Eb:.6f}) frames={glob_best[1].tolist()} "
        f"S={S.tolist()} flux nontriv={fnb:.4f} traceless={ftb:.4f} -1={fmb:.4f}")
    overall = max(Eu.max(), Em.max(), glob_best[0])
    log(f" SUMMARY item 3: max flux-matched E_per found = {max(Em.max(), glob_best[0]):.6f};  overall max over the {len(res_u)} uniform decorations = {Eu.max():.6f};  "
        f"any flux-matched > 8.770: {max(Em.max(), glob_best[0]) > 8.770};  > 8.5: {max(Em.max(), glob_best[0]) > 8.5};  > 8.18: {max(Em.max(), glob_best[0]) > 8.18}")
    return res_m, glob_best

# =====================================================================================================================
# 6. Regression (claim d) and bijections (claim e)
# =====================================================================================================================
def stage_regress():
    log("=" * 110); log("6. CLAIM (d): own least-squares regression on the records")
    uniq = dedupe(load_records())
    E = np.array([r['E'] for r in uniq]); ft = np.array([r['f_traceless'] for r in uniq]); fm = np.array([r['f_minus1'] for r in uniq]); fn = np.array([r['f_nontriv'] for r in uniq])
    A = np.c_[np.ones_like(E), ft, fm]
    coef, *_ = np.linalg.lstsq(A, E, rcond=None); res = E - A @ coef
    pred = coef[0] + coef[1] * 55 / 144 + coef[2] * 13 / 144
    log(f" n={len(E)} distinct decorations: E_per ~ {coef[0]:.4f} + {coef[1]:.4f} f_traceless + {coef[2]:.4f} f_-1 ; rms residual {np.sqrt(np.mean(res**2)):.4f}; sd(E)={E.std():.4f}; "
        f"R^2={1-np.var(res)/np.var(E):.4f}; prediction at FR30 fractions: {pred:.4f}  (claim: -1.904 + 14.303 ft + 30.696 fm, rms 0.532, 6.330)")
    log(f" residual max={res.max():.3f} min={res.min():.3f}; 95th percentile |res|={np.percentile(np.abs(res),95):.3f}; fraction with |res|>2: {np.mean(np.abs(res)>2):.4f}")
    log(f" Pearson corr(E, f_nontriv)={np.corrcoef(E,fn)[0,1]:.4f}, corr(E, f_traceless)={np.corrcoef(E,ft)[0,1]:.4f}, corr(E, f_-1)={np.corrcoef(E,fm)[0,1]:.4f}")
    # sanity: same regression per k, and with f_nontriv only
    for k in (2, 4, 8):
        s = np.array([r['k'] == k for r in uniq])
        if s.sum() > 10:
            c, *_ = np.linalg.lstsq(A[s], E[s], rcond=None); rr = E[s] - A[s] @ c
            log(f"   k={k} only (n={s.sum()}): coef={np.round(c,3).tolist()} rms={np.sqrt(np.mean(rr**2)):.3f} pred@FR30={c[0]+c[1]*55/144+c[2]*13/144:.3f}")
    c1, *_ = np.linalg.lstsq(np.c_[np.ones_like(E), fn], E, rcond=None); r1 = E - np.c_[np.ones_like(E), fn] @ c1
    log(f"   one-variable fit E ~ {c1[0]:.3f} + {c1[1]:.3f} f_nontriv: rms={np.sqrt(np.mean(r1**2)):.3f}, pred@17/36={c1[0]+c1[1]*17/36:.3f}")
    # the regression is a summary of the census, not a predictor: residual spread among flux-matched
    mt = np.array([flux_matched(r['f_nontriv'], r['f_traceless'], r['f_minus1']) for r in uniq])
    log(f"   among the {mt.sum()} flux-matched records: E range [{E[mt].min():.4f},{E[mt].max():.4f}], regression predictions range [{(A@coef)[mt].min():.3f},{(A@coef)[mt].max():.3f}]")

def stage_bijections(rng, nsample=200):
    log("=" * 110); log("7. CLAIM (e): FR30 level-1 frames on the cosets of 2L (own code), natural bijection + random bijections")
    cr = crystal(2 * I3)
    eps = [tuple(int(x) % 2 for x in m) for m in cr.reps]
    nat = [0 if e == (1, 1, 1) else 1 + U3.index(e) for e in eps]
    log(f" cosets of 2L (reps m): {[m.tolist() for m in cr.reps]}; eps=m mod 2: {eps}; natural bijection (FR30 frame index per coset): {nat}  (B2a label order: [1,2,3,4,5,6,7,0])")
    fr = np.array([FR30_IDX[p] for p in nat])
    t = time.time(); r = cr.band_bottom(fr, ngrid=12); fn, ft, fm = cr.flux_fractions(fr)
    log(f" natural bijection: E_per={r['E']:.9f} (12^3 grid + refinement) at theta={np.round(r['theta'],5).tolist()}; flux nontriv={fn:.4f} traceless={ft:.4f} -1={fm:.4f}  (claim: 10.644234146; record flux 0.7083/0.5278/0.1806)")
    Es = []
    for i in range(nsample):
        perm = rng.permutation(8); fr = np.array([FR30_IDX[p] for p in perm])
        Es.append(cr.band_bottom(fr)['E'])
    Es = np.array(Es)
    log(f" {nsample} random bijections ({time.time()-t:.1f}s): E_per min={Es.min():.6f} max={Es.max():.6f} mean={Es.mean():.4f}; all in [9.613979, 14.176070]: {bool(Es.min() >= 9.613979-1e-6 and Es.max() <= 14.176070+1e-6)}; all > 8.770: {bool(Es.min() > 8.770)}")
    chunks = sorted(glob.glob(os.path.join(HERE, 'results', 'phase5a_periodic_control_bijections_chunk*.npy')))
    if chunks:
        Ec = np.concatenate([np.load(c) for c in chunks])
        log(f" B2a stage-C arrays: {len(Ec)} values, min={Ec.min():.6f} max={Ec.max():.6f}, mean={Ec.mean():.5f}  (claim: [9.613979, 14.176070]); my {nsample} values all occur in the arrays (|diff|<1e-6): "
            f"{all(np.min(np.abs(Ec - e)) < 1e-6 for e in Es)}; max over my sample of min|E_mine - E_C|: {max(np.min(np.abs(Ec - e)) for e in Es):.2e}")
    # also: permutations hitting the recorded extremes? report the extreme values I find vs claimed bounds
    log(f" 2L: 2L subset of ker phi, index 8; FR30 frames are 8 specific SO(3,Z) elements: {sorted(FR30_IDX)} (centre and child (0,0,0) are both the identity)")

# =====================================================================================================================
def main():
    global _fh
    stages = sys.argv[1:] or ['crystal', 'records', 'search', 'regress', 'bijections']
    os.makedirs(os.path.dirname(OUT), exist_ok=True)
    _fh = open(OUT, 'a')
    log("#" * 110); log(f"# phase5a_d2_census_verify.py  stages={stages}  cmd: OMP_NUM_THREADS=1 python3 -u -I audit/phase5a_d2_census_verify.py {' '.join(sys.argv[1:])}")
    log(f"# numpy {np.__version__}; seeds: numpy default_rng(20261021)")
    rng = np.random.default_rng(20261021)
    if 'crystal' in stages:
        t = time.time(); stage_crystal(); q8_tables_check(rng); crystal_torus_checks(); log(f"[crystal stage wall {time.time()-t:.1f}s]")
    if 'records' in stages:
        t = time.time(); stage_records(rng); log(f"[records stage wall {time.time()-t:.1f}s]")
    if 'search' in stages:
        t = time.time(); stage_search(rng); log(f"[search stage wall {time.time()-t:.1f}s]")
    if 'regress' in stages:
        t = time.time(); stage_regress(); log(f"[regress stage wall {time.time()-t:.1f}s]")
    if 'bijections' in stages:
        t = time.time(); stage_bijections(rng); log(f"[bijections stage wall {time.time()-t:.1f}s]")
    log(f"[total wall {time.time()-T0:.1f}s]")

if __name__ == '__main__':
    main()
