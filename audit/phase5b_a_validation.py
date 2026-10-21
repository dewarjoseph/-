#!/usr/bin/env python3
"""Phase V-B, Workstream A: reproduction and validation of the Phase V-A baseline.

Everything in this file is written for Phase V-B.  Only the DEFINITIONS of the object are imported from the audited
primitives of audit/independent_clifford_q8_audit.py (FR30 table, U3, tiles_at_level, panel_edges, clifford_link,
q8label); every one of them is re-derived here as well (own pose recursion, own owner map / panel list, own Pauli
link) and compared, so that each item of the baseline table can be labelled

    'independent implementation'  (own code, different design from the Phase V-A scripts),
    'same implementation re-run'  (a Phase V-A script executed again, from a scratch copy when it writes results),
    'read from artifact'          (a number read from a stored file, not recomputed).

Design choices that differ from the Phase V-A code:
  * plaquettes are enumerated PER TILE and PER CUBE (each lattice edge is attributed to the cube at its lower corner
    in the transverse plane) and evaluated with explicit 2x2 Pauli-matrix products and trace/axis classification,
    not by grid slicing with integer Q8 codes (phase5a_flux_vs_edge.py) nor by lattice-edge slicing with abstract
    (sign, basis) pairs (phase5a_independent_enumerator.py);
  * the Hamiltonian is assembled from the panel list as 2x2 blocks into a COO triplet list by this file;
  * the exact LDL^* certificates use the REAL symmetric embedding [[Re, -Im], [Im, Re]] of the Hermitian form with
    fractions.Fraction, not the complex-pair elimination of phase5a_star_closure_lower_bound.py;
  * the periodic chair crystal is rebuilt from the definition (phi(x,y,z) = x+2y+4z mod 7), with its own coset
    bookkeeping, its own real-space torus operator and its own Bloch blocks (read from the D2 script only to decode
    the HNF / coset-order / SO(3,Z)-index conventions of the stored records).

Usage (run from the repository root, python3 -u -I):
    python3 -u -I audit/phase5b_a_validation.py geometry        (a) own enumerator, levels 1-4 (+5 optionally)
    python3 -u -I audit/phase5b_a_validation.py bottoms         (b),(e) pinned bottoms levels 2-5, IPR, interfaces
    python3 -u -I audit/phase5b_a_validation.py periodic        (c) Lambda_7 crystal: natural bijection and D2 record
    python3 -u -I audit/phase5b_a_validation.py controls        (d) seeds 1 and 108 at level 4, flux table re-run
    python3 -u -I audit/phase5b_a_validation.py lowerbound      (f) exact LDL^* certificates and star sums
Results: audit/results/phase5b_a_<part>.json / .txt
"""
import os, sys, time, json, itertools, collections, resource
from fractions import Fraction
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
RES = os.path.join(HERE, 'results')
import numpy as np, scipy.sparse as sps, scipy.sparse.linalg as spl, scipy.linalg as sla
from independent_clifford_q8_audit import FR30, U3, tiles_at_level, panel_edges, clifford_link, q8label, perm_mat

# ============================================================================================ 0. basics
SIG = (np.array([[0, 1], [1, 0]], complex), np.array([[0, -1j], [1j, 0]], complex), np.array([[1, 0], [0, -1]], complex))
I2 = np.eye(2, dtype=complex)
E3 = [np.array(v, dtype=int) for v in ((1, 0, 0), (0, 1, 0), (0, 0, 1))]
PERMS = list(itertools.permutations(range(3)))
def perm_sign(p):
    s = 1
    for i in range(3):
        for j in range(i + 1, 3):
            if p[i] > p[j]: s = -s
    return s
EVEN = [p for p in PERMS if perm_sign(p) == 1]; ODD = [p for p in PERMS if perm_sign(p) == -1]

def rss_gb(): return resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 1e6

def sdot(u): return u[0] * SIG[0] + u[1] * SIG[1] + u[2] * SIG[2]

def pauli_link(Ma, Mb, n):
    """Own link: C_ab = (sigma . M_a^T n)(sigma . M_b^T n)."""
    return sdot(Ma.T @ n) @ sdot(Mb.T @ n)

def classify(W):
    """Conjugacy class of W in Q8 from the matrix: '+1', '-1', or the traceless axis 'i','j','k' (W = +-i sigma_m)."""
    tr = W[0, 0] + W[1, 1]
    if abs(tr - 2) < 1e-9: return '+1'
    if abs(tr + 2) < 1e-9: return '-1'
    assert abs(tr) < 1e-9, tr
    # W = i s sigma_m  ->  -i W = s sigma_m
    X = -1j * W
    if abs(X[0, 1] - X[1, 0]) < 1e-9 and abs(X[0, 1]) > 0.5: return 'i'
    if abs(X[0, 1] + X[1, 0]) < 1e-9 and abs(X[0, 1]) > 0.5: return 'j'
    assert abs(X[0, 0]) > 0.5 and abs(X[0, 1]) < 1e-9, X
    return 'k'

def signed_label(W):
    """Signed Q8 label of a matrix in the MATRIX convention: '+i' means +i*sigma_1 (= quaternion -i)."""
    return q8label(W)

# ============================================================================================ 1. own geometry
def own_poses(frames, level):
    """Own pose recursion (lists of integer tuples; depth-first, same child order as the definition).
    Child maps: centre (P(pi_0), (1,1,1)); octant v: (D_v P(pi_v), 4v).  Pose (G,T) -> (G g_c, 2T + G t_c)."""
    ops = [(perm_mat(frames['0']), np.array([1, 1, 1]))]
    for v in U3:
        ops.append((np.diag([1 - 2 * v[0], 1 - 2 * v[1], 1 - 2 * v[2]]) @ perm_mat(frames[v]), 4 * np.array(v)))
    poses = [(np.eye(3, dtype=int), np.zeros(3, dtype=int))]
    for _ in range(level):
        poses = [(G @ g, 2 * T + G @ t) for G, T in poses for g, t in ops]
    return poses

def own_cubes(G, T):
    """Cubes (lower corners) of the chair with pose (G,T): centres M(u + 1/2) + T, u in U3, i.e. corner (G(2u+1) + 2T - 1)/2."""
    out = []
    for u in U3:
        c = G @ np.array([2 * u[0] + 1, 2 * u[1] + 1, 2 * u[2] + 1]) + 2 * T - 1
        assert (c % 2 == 0).all()
        out.append(tuple(int(x) for x in c // 2))
    return out

def own_owner(tiles):
    owner = {}
    for a, (_, _, cs) in enumerate(tiles):
        for c in cs:
            assert c not in owner, 'overlap'
            owner[c] = a
    return owner

def own_panels(tiles, owner=None):
    """Panels as (a, b, axis, cube_a) with b = owner of cube_a + e_axis != a, for every cube and every axis (one
    orientation per unit face: from the lower cube to the upper cube)."""
    owner = owner or own_owner(tiles)
    out = []
    for c, a in owner.items():
        for ax in range(3):
            c2 = (c[0] + (ax == 0), c[1] + (ax == 1), c[2] + (ax == 2))
            b = owner.get(c2)
            if b is not None and b != a: out.append((a, b, ax, c))
    return out

def link_table(tiles):
    """Cache of link matrices by (frame key a, frame key b, axis)."""
    cache = {}
    def link(a, b, ax):
        Ga, Gb = tiles[a][0], tiles[b][0]
        key = (Ga.tobytes(), Gb.tobytes(), ax)
        C = cache.get(key)
        if C is None: C = pauli_link(Ga, Gb, E3[ax]); cache[key] = C
        return C
    return link

def own_plaquettes(tiles, owner=None, classes_only=False):
    """PER-TILE / PER-CUBE enumeration of the inter-tile plaquettes.
    For every tile a, every cube c of a and every transverse pair (i,j) the lattice edge with lower-corner cube c
    (parallel to the third axis) is surrounded by c, c+e_i, c+e_i+e_j, c+e_j.  The plaquette is counted iff all four
    cubes are present (in the patch) and they belong to >= 2 tiles.  Holonomy W = L(c,c1) L(c1,c2) L(c2,c3) L(c3,c)
    with L = I inside a tile and L = Pauli link across a panel (normal = step direction); class by trace/axis.
    Returns (count per class, list of (owners 4-tuple, class) if not classes_only)."""
    owner = owner or own_owner(tiles)
    link = link_table(tiles)
    counts = collections.Counter(); recs = []
    for a, (_, _, cs) in enumerate(tiles):
        for c in cs:
            for (i, j) in ((0, 1), (1, 2), (0, 2)):
                c1 = (c[0] + (i == 0), c[1] + (i == 1), c[2] + (i == 2))
                c2 = (c1[0] + (j == 0), c1[1] + (j == 1), c1[2] + (j == 2))
                c3 = (c[0] + (j == 0), c[1] + (j == 1), c[2] + (j == 2))
                o1 = owner.get(c1); o2 = owner.get(c2); o3 = owner.get(c3)
                if o1 is None or o2 is None or o3 is None: continue
                if o1 == a and o2 == a and o3 == a: continue
                W = I2
                for (oa, ob, ax) in ((a, o1, i), (o1, o2, j), (o2, o3, i), (o3, a, j)):
                    if oa != ob: W = W @ link(oa, ob, ax)
                cl = classify(W); counts[cl] += 1
                if not classes_only: recs.append(((a, o1, o2, o3), cl, (c, i, j)))
    return counts, recs

def class_summary(counts):
    N = sum(counts.values()); trl = counts['i'] + counts['j'] + counts['k']
    return dict(N=N, plus=counts['+1'], minus=counts['-1'], i=counts['i'], j=counts['j'], k=counts['k'], traceless=trl,
                f_nontriv=(N - counts['+1']) / N, f_traceless=trl / N, f_minus=counts['-1'] / N)

# ============================================================================================ 2. own operator
def own_H(tiles, panels, pinned=True, bulk=24.0, link=None):
    """Sparse H = diag - A assembled by this file from the panel list; A_ab = sum over panels (a,b) of C_ab, C_ba = C_ab^+.
    pinned: diagonal 24 for every tile; free: diagonal = number of panels at the tile."""
    n = len(tiles); link = link or link_table(tiles)
    m = len(panels)
    rows = np.empty(8 * m + 2 * n, dtype=np.int64); cols = np.empty_like(rows); vals = np.empty(8 * m + 2 * n, dtype=complex)
    k = 0
    deg = np.zeros(n, int)
    for (a, b, ax, _) in panels:
        C = link(a, b, ax); deg[a] += 1; deg[b] += 1
        for r in range(2):
            for c in range(2):
                rows[k] = 2 * a + r; cols[k] = 2 * b + c; vals[k] = -C[r, c]; k += 1
                rows[k] = 2 * b + c; cols[k] = 2 * a + r; vals[k] = -np.conj(C[r, c]); k += 1
    d = np.full(n, bulk) if pinned else deg.astype(float)
    idx = np.arange(2 * n)
    rows[k:] = idx; cols[k:] = idx; vals[k:] = np.repeat(d, 2)
    H = sps.coo_matrix((vals, (rows, cols)), shape=(2 * n, 2 * n)).tocsr()
    H.sum_duplicates()
    return H, deg

def hermiticity_defect(H):
    D = (H - H.getH()).tocsr(); D.eliminate_zeros()
    return D.nnz, (abs(D).max() if D.nnz else 0.0)

def gaussian_integer_defect(H):
    v = H.data
    return float(np.abs(v - np.rint(v.real) - 1j * np.rint(v.imag)).max()) if len(v) else 0.0

def solve_dense(H, k=4):
    w, V = sla.eigh(H.toarray())
    return finalize(H, w[:k], V[:, :k])

def finalize(H, w, V):
    V = V / np.linalg.norm(V, axis=0); HV = H @ V
    lam = np.real(np.einsum('ij,ij->j', V.conj(), HV)); res = np.linalg.norm(HV - V * lam, axis=0)
    o = np.argsort(lam); return lam[o], V[:, o], res[o]

def solve_shift_invert(H, k=4, sigma=0.0, tol=1e-12):
    """scipy eigsh in shift-invert mode (sparse LU of H - sigma)."""
    w, V = spl.eigsh(H, k=k, sigma=sigma, which='LM', tol=tol, maxiter=5000)
    return finalize(H, w, V)

def solve_lobpcg(H, k=4, block=6, seed=1, tol=1e-7, maxiter=4000):
    rng = np.random.default_rng(seed); N = H.shape[0]
    X = rng.standard_normal((N, block)) + 1j * rng.standard_normal((N, block))
    dinv = 1.0 / H.diagonal().real
    M = spl.LinearOperator(H.shape, matvec=lambda v: dinv * v, matmat=lambda B: dinv[:, None] * B, dtype=complex)
    import warnings
    with warnings.catch_warnings():
        warnings.simplefilter('ignore')
        w, V = spl.lobpcg(H, X, M=M, largest=False, tol=tol, maxiter=maxiter)
    lam, V, res = finalize(H, w, V); return lam[:k], V[:, :k], res[:k]

# ============================================================================================ 3. ground-state diagnostics
def tile_density(psi):
    p = np.abs(psi[0::2]) ** 2 + np.abs(psi[1::2]) ** 2; return p / p.sum()

def interface_masks(n, panels, level):
    """I_d (d=1..L): tiles incident to a panel joining tiles with different depth-d ancestors; ancestor = index // 8^(L-d)
    in the depth-first order of the pose recursion (the first 8^(L-d) tiles are the (0,0,0)...-word subtree, etc.)."""
    a = np.array([p[0] for p in panels]); b = np.array([p[1] for p in panels]); out = {}
    for d in range(1, level + 1):
        q = 8 ** (level - d); cross = (a // q) != (b // q)
        m = np.zeros(n, bool); m[a[cross]] = True; m[b[cross]] = True; out[d] = m
    return out

def diagnostics(p, level, masks, deg=None, bulk=24):
    n = len(p); out = {'n': n, 'ipr': float((p ** 2).sum()), 'ipr_n': float((p ** 2).sum() * n)}
    S2 = {}; D2 = {}; prev = 1.0
    for d in range(1, level + 1):
        W = p.reshape(8 ** d, 8 ** (level - d)).sum(axis=1); s2 = float((W ** 2).sum()); S2[d] = s2; D2[d] = float(np.log2(prev / s2)); prev = s2
    out['S2'] = S2; out['inv_S2'] = {d: 1 / s for d, s in S2.items()}; out['D2_box'] = D2
    out['interface_weight'] = {d: float(p[m].sum()) for d, m in masks.items()}
    out['interface_fraction'] = {d: float(m.mean()) for d, m in masks.items()}
    out['interface_enrichment'] = {d: out['interface_weight'][d] / out['interface_fraction'][d] for d in masks}
    if deg is not None: out['boundary_weight'] = float(p[deg < bulk].sum()); out['boundary_fraction'] = float((deg < bulk).mean())
    return out

# ============================================================================================ 4. random decorations
def own_random_decoration(seed):
    """Re-implementation of phase5a_scaling_controls.random_decoration: default_rng(seed); centre frame from the 3 even
    permutations (itertools order), octant v from EVEN if sum(v) even else ODD; redraw if equal to FR30."""
    rng = np.random.default_rng(seed)
    while True:
        d = {'0': EVEN[rng.integers(3)]}
        for v in U3: d[v] = (EVEN if sum(v) % 2 == 0 else ODD)[rng.integers(3)]
        if d != FR30: return d

# ============================================================================================ 5. Lambda_7 chair crystal
class ChairCrystal:
    """Chairs x + U3 for x in ker(phi), phi(c) = c0 + 2 c1 + 4 c2 mod 7, decorated with frames constant on cosets of a
    sublattice L' of L = ker(phi).  L basis rows BL (ambient), L' basis rows S @ BL with S an upper-triangular HNF in
    L-coordinates; coset of m (L-coords) = canonical representative in [0,d1)x[0,d2)x[0,d3) by row reduction; the
    coset ORDER (needed only to decode stored 'frames' lists) is the sort order of the key (k S^{-1})^T m mod k."""
    BL = np.array([[1, 1, 1], [2, 1, -1], [-1, 2, 1]], dtype=int)
    def __init__(self, S):
        self.S = S = np.asarray(S, dtype=int); self.k = int(round(np.linalg.det(S)))
        self.res2u = {}
        for u in U3: self.res2u[self.phi(u)] = np.array(u, dtype=int)
        assert sorted(self.res2u) == list(range(7))
        assert all(self.phi(r) == 0 for r in self.BL) and abs(round(np.linalg.det(self.BL))) == 7
        self.BLinvT = np.linalg.inv(self.BL.T.astype(float))
        adjT = np.rint(self.k * np.linalg.inv(S.astype(float))).astype(int).T
        reps = [np.array(m) for m in itertools.product(range(S[0, 0]), range(S[1, 1]), range(S[2, 2]))]
        keyed = sorted((tuple(int(x) for x in (adjT @ m) % self.k), tuple(int(x) for x in m)) for m in reps)
        self.reps = [np.array(m) for _, m in keyed]; self.rep_index = {m: i for i, (_, m) in enumerate(keyed)}
        self.Bp = S @ self.BL                                   # L' basis rows, ambient
        self.BpinvT = np.linalg.inv(self.Bp.T.astype(float))
    @staticmethod
    def phi(c): return (int(c[0]) + 2 * int(c[1]) + 4 * int(c[2])) % 7
    def owner_point(self, c):
        c = np.asarray(c, dtype=int); return c - self.res2u[self.phi(c)]
    def to_L(self, x):
        m = self.BLinvT @ np.asarray(x, float); mi = np.rint(m).astype(int); assert np.allclose(m, mi); return mi
    def reduce(self, m):
        m = np.array(m, dtype=int)
        for i in range(3):
            m = m - (m[i] // self.S[i, i]) * self.S[i]
        return m
    def coset(self, m): return self.rep_index[tuple(int(x) for x in self.reduce(m))]
    def coset_of_point(self, x): return self.coset(self.to_L(x))
    # ---- hops of one chair: (coset a, coset b, ambient displacement of chair b relative to chair a, normal) ----
    def hops(self):
        out = []
        for a, m in enumerate(self.reps):
            x = m @ self.BL
            for u in U3:
                c = x + np.array(u)
                for ax in range(3):
                    for s in (1, -1):
                        c2 = c.copy(); c2[ax] += s
                        y = self.owner_point(c2)
                        if (y == x).all(): continue
                        out.append((a, self.coset_of_point(y), y - x, s * E3[ax]))
        return out
    def frames_matrices(self, frames, so3z):
        return [so3z[f] for f in frames]
    def bloch_bottom(self, frames, so3z, ngrid=8, nstart=3):
        """H(q) = 24 - sum_hops e^{i q.d} C_ab placed in block (a,b); minimum of the lowest band over the Brillouin zone."""
        import scipy.optimize as sopt
        M = self.frames_matrices(frames, so3z); k = self.k; hops = self.hops()
        assert len(hops) == 24 * k
        blocks = np.zeros((len(hops), 2 * k, 2 * k), complex); D = np.zeros((len(hops), 3))
        for h, (a, b, d, n) in enumerate(hops):
            blocks[h, 2 * a:2 * a + 2, 2 * b:2 * b + 2] = pauli_link(M[a], M[b], n); D[h] = d
        def Hq(q):
            ph = np.exp(1j * (D @ q)); return 24 * np.eye(2 * k) - np.einsum('h,hij->ij', ph, blocks)
        def f(q): return np.linalg.eigvalsh(Hq(q))[0]
        th = np.array(list(itertools.product(np.arange(ngrid) / ngrid, repeat=3)))
        Q = (2 * np.pi * np.linalg.solve(self.Bp.astype(float), th.T)).T       # Bp q = 2 pi theta
        e0 = np.array([f(q) for q in Q]); order = np.argsort(e0)
        best = (float(e0[order[0]]), Q[order[0]])
        for s in order[:nstart]:
            r = sopt.minimize(f, Q[s], method='Nelder-Mead', options=dict(xatol=1e-10, fatol=1e-14, maxiter=6000))
            r2 = sopt.minimize(f, r.x, method='BFGS', options=dict(gtol=1e-11))
            for val, q in ((r.fun, r.x), (r2.fun, r2.x)):
                if val < best[0] - 1e-14: best = (float(val), q)
        return dict(E=best[0], theta=((self.Bp @ best[1]) / (2 * np.pi) % 1.0).tolist(), grid_min=float(e0.min()), Hq=Hq)
    def torus(self, frames, so3z, N):
        """Real-space pinned operator on the torus Z^3 / N L' with chairs indexed by (coset, cell alpha in (Z/N)^3)."""
        M = self.frames_matrices(frames, so3z); k = self.k
        idx = {}
        for c in range(k):
            for al in itertools.product(range(N), repeat=3): idx[(c, al)] = len(idx)
        def chair_of_point(y):
            c = self.coset_of_point(y); al = self.BpinvT @ (y - self.reps[c] @ self.BL).astype(float)
            ali = np.rint(al).astype(int); assert np.allclose(al, ali); return c, tuple(int(x) % N for x in ali)
        tiles = []; panels = []; cube_owner = {}
        for c, m in enumerate(self.reps):
            for al in itertools.product(range(N), repeat=3):
                x = m @ self.BL + np.array(al) @ self.Bp; a = idx[(c, al)]
                tiles.append((M[c], x));
        rows, cols, vals = [], [], []
        npan = 0; plaq = collections.Counter()
        for c, m in enumerate(self.reps):
            for al in itertools.product(range(N), repeat=3):
                x = m @ self.BL + np.array(al) @ self.Bp; a = idx[(c, al)]
                for u in U3:
                    cu = x + np.array(u)
                    for ax in range(3):
                        for s in (1, -1):
                            c2 = cu.copy(); c2[ax] += s; y = self.owner_point(c2)
                            if (y == x).all(): continue
                            cb, alb = chair_of_point(y); b = idx[(cb, alb)]
                            C = pauli_link(M[c], M[cb], s * E3[ax]); npan += 1
                            for r in range(2):
                                for t in range(2): rows.append(2 * a + r); cols.append(2 * b + t); vals.append(-C[r, t])
                    # plaquettes owned by cube cu (lower corner): classes on the torus (one fundamental domain = al == 0)
                    if al == (0, 0, 0):
                        for (i, j) in ((0, 1), (1, 2), (0, 2)):
                            ring = [cu, cu + E3[i], cu + E3[i] + E3[j], cu + E3[j]]
                            own = [self.owner_point(q) for q in ring]
                            if all((o == own[0]).all() for o in own): continue
                            W = I2
                            for t in range(4):
                                oa, ob = own[t], own[(t + 1) % 4]
                                if (oa == ob).all(): continue
                                W = W @ pauli_link(M[self.coset_of_point(oa)], M[self.coset_of_point(ob)], ring[(t + 1) % 4] - ring[t])
                            plaq[classify(W)] += 1
        n = len(idx)
        H = sps.coo_matrix((vals, (rows, cols)), shape=(2 * n, 2 * n)).tocsr() + 24.0 * sps.identity(2 * n, format='csr')
        return H, npan, plaq

def so3z_list():
    """SO(3,Z) in the enumeration order of the B2a/D2 records: diag(s) P(p), p in itertools order, s in {+1,-1}^3, det=+1."""
    out = [np.diag(s) @ perm_mat(p) for p in PERMS for s in itertools.product((1, -1), repeat=3)]
    out = [g for g in out if round(np.linalg.det(g)) == 1]; assert len(out) == 24; return out

# ============================================================================================ 6. exact LDL^* certificates
def real_embedding(H):
    """Hermitian H (Gaussian integers) -> real symmetric [[Re, -Im], [Im, Re]] as Fractions."""
    n = H.shape[0]; R = np.rint(H.real).astype(int); Im = np.rint(H.imag).astype(int)
    assert np.allclose(R + 1j * Im, H, atol=1e-12)
    A = [[Fraction(0)] * (2 * n) for _ in range(2 * n)]
    for i in range(n):
        for j in range(n):
            A[i][j] = Fraction(int(R[i, j])); A[i + n][j + n] = Fraction(int(R[i, j]))
            A[i][j + n] = Fraction(-int(Im[i, j])); A[i + n][j] = Fraction(int(Im[i, j]))
    return A

def exact_pd(A, mu):
    """Is the symmetric rational matrix A - mu I positive definite?  Exact LDL^T: all pivots > 0."""
    n = len(A); B = [row[:] for row in A]
    for i in range(n): B[i][i] -= mu
    for k in range(n):
        piv = B[k][k]
        if piv <= 0: return False
        for i in range(k + 1, n):
            if B[i][k] == 0: continue
            l = B[i][k] / piv
            Bi = B[i]; Bk = B[k]
            for j in range(k + 1, n):
                if Bk[j] != 0: Bi[j] -= l * Bk[j]
    return True

def exact_min_pivot_sign(A):
    """Returns True iff A (rational symmetric) is positive SEMIdefinite-singular-or-indefinite detected by a non-positive pivot
    (used to confirm that 'flat' forms are indeed singular: the first non-positive pivot is exactly 0 for PSD)."""
    n = len(A); B = [row[:] for row in A]
    for k in range(n):
        piv = B[k][k]
        if piv < 0: return 'indefinite'
        if piv == 0:
            if any(B[i][k] != 0 for i in range(k + 1, n)): return 'indefinite'
            continue
        for i in range(k + 1, n):
            if B[i][k] == 0: continue
            l = B[i][k] / piv
            for j in range(k + 1, n):
                if B[k][j] != 0: B[i][j] -= l * B[k][j]
    return 'psd-singular'

def plaquette_form(cycle_tiles, cycle_links):
    """h_e for the 4-cycle (tiles t0..t3, link C_s across the face (t_s, t_{s+1}) or None inside a tile) on the
    distinct tiles; returns (H, labels)."""
    labels = sorted(set(cycle_tiles)); loc = {t: i for i, t in enumerate(labels)}; n = len(labels)
    H = np.zeros((2 * n, 2 * n), complex)
    for s in range(4):
        t1, t2 = cycle_tiles[s], cycle_tiles[(s + 1) % 4]
        if t1 == t2: continue
        a, b = loc[t1], loc[t2]; C = cycle_links[s]
        H[2 * a:2 * a + 2, 2 * a:2 * a + 2] += I2; H[2 * b:2 * b + 2, 2 * b:2 * b + 2] += I2
        H[2 * a:2 * a + 2, 2 * b:2 * b + 2] -= C; H[2 * b:2 * b + 2, 2 * a:2 * a + 2] -= C.conj().T
    return H, labels

def all_edges_with_forms(tiles, owner, link):
    """Every lattice edge of the patch whose 4 cubes are present and belong to >= 2 tiles: (signature, tiles).
    signature = (pattern of tile identities in cyclic order, signed link labels), the key for lambda_min caching."""
    out = []
    for a, (_, _, cs) in enumerate(tiles):
        for c in cs:
            for (i, j) in ((0, 1), (1, 2), (0, 2)):
                c1 = (c[0] + (i == 0), c[1] + (i == 1), c[2] + (i == 2))
                c2 = (c1[0] + (j == 0), c1[1] + (j == 1), c1[2] + (j == 2))
                c3 = (c[0] + (j == 0), c[1] + (j == 1), c[2] + (j == 2))
                o1 = owner.get(c1); o2 = owner.get(c2); o3 = owner.get(c3)
                if o1 is None or o2 is None or o3 is None: continue
                if o1 == a and o2 == a and o3 == a: continue
                cyc = (a, o1, o2, o3); axes = (i, j, i, j)
                labels = sorted(set(cyc)); loc = {t: k for k, t in enumerate(labels)}
                pattern = tuple(loc[t] for t in cyc); links = []; sig_links = []
                for s in range(4):
                    t1, t2 = cyc[s], cyc[(s + 1) % 4]
                    if t1 == t2: links.append(None); sig_links.append('same'); continue
                    C = link(t1, t2, axes[s]) if s < 2 else link(t2, t1, axes[s]).conj().T
                    # steps 0,1 go +e_i, +e_j (lower -> upper cube, our stored orientation); steps 2,3 go -e_i, -e_j
                    links.append(C); sig_links.append(signed_label(C))
                out.append(((pattern, tuple(sig_links)), cyc, links))
    return out

# ============================================================================================ 7. CLI parts
def say_factory(tag):
    lines = []
    def say(s=''):
        print(s, flush=True); lines.append(s)
    def dump(obj):
        with open(os.path.join(RES, f'phase5b_a_{tag}.txt'), 'w') as f: f.write('\n'.join(lines) + '\n')
        with open(os.path.join(RES, f'phase5b_a_{tag}.json'), 'w') as f: json.dump(obj, f, indent=1, default=_conv)
    return say, dump
def _conv(o):
    if isinstance(o, (np.integer,)): return int(o)
    if isinstance(o, (np.floating,)): return float(o)
    if isinstance(o, np.ndarray): return o.tolist()
    if isinstance(o, Fraction): return str(o)
    if isinstance(o, (set, frozenset)): return sorted(o)
    if isinstance(o, dict): return {str(k): v for k, v in o.items()}
    raise TypeError(type(o))

def build(level, frames=FR30):
    tiles = tiles_at_level(frames, level); owner = own_owner(tiles); panels = own_panels(tiles, owner); link = link_table(tiles)
    return tiles, owner, panels, link

def part_geometry(maxlevel):
    say, dump = say_factory('geometry'); out = {}
    say("PHASE V-B / A (a): own per-tile Pauli-matrix plaquette enumerator versus the Phase V-A class counts")
    dossier = {1: (60, 26, 3, 12, 7, 12), 2: (792, 385, 42, 124, 117, 124), 3: (7728, 3945, 530, 1020, 1213, 1020),
               4: (67680, 35161, 5394, 8188, 10749, 8188), 5: (565440, 296121, 48146, 65532, 90109, 65532)}
    # link convention check: own pauli_link == audited clifford_link on all 24x24x3 combinations
    so3 = so3z_list(); bad = 0
    for Ma in so3:
        for Mb in so3:
            for ax in range(3): bad += not np.allclose(pauli_link(Ma, Mb, E3[ax]), clifford_link(Ma, Mb, E3[ax]))
    say(f" own pauli_link vs audited clifford_link on all 24x24x3 (M_a, M_b, axis): mismatches = {bad}")
    out['link_mismatches'] = bad
    for L in range(1, maxlevel + 1):
        t0 = time.time(); poses = own_poses(FR30, L); tiles = tiles_at_level(FR30, L)
        same_poses = len(poses) == len(tiles) and all((G == t[0]).all() and (T == t[1]).all() for (G, T), t in zip(poses, tiles))
        cubes_ok = all(set(own_cubes(G, T)) == set(t[2]) for (G, T), t in zip(poses, tiles))
        owner = own_owner(tiles); N = 2 ** (L + 1)
        box = {c for c in itertools.product(range(N), repeat=3) if not all(x >= N // 2 for x in c)}
        fills = set(owner) == box
        panels = own_panels(tiles, owner)
        _, edges = panel_edges(tiles)
        ms_own = collections.Counter((a, b, ax) for a, b, ax, _ in panels)
        ms_rep = collections.Counter((a, b, int(np.argmax(nf))) for a, b, nf, _, _ in edges)
        counts, _ = own_plaquettes(tiles, owner, classes_only=True); cs = class_summary(counts)
        got = (cs['N'], cs['plus'], cs['minus'], cs['i'], cs['j'], cs['k'])
        say(f" level {L}: tiles {len(tiles)} (=8^L {len(tiles)==8**L}), poses identical to tiles_at_level {same_poses}, cube sets identical {cubes_ok}, "
            f"cubes {len(owner)} (=7*8^L {len(owner)==7*8**L}) fill [0,2^(L+1))^3 \\ [2^L,2^(L+1))^3: {fills}; panels {len(panels)} (=12(8^L-4^L): {len(panels)==12*(8**L-4**L)}), "
            f"panel multiset == panel_edges: {ms_own == ms_rep}")
        say(f"    inter-tile plaquettes (N,+1,-1,i,j,k) own = {got}; dossier = {dossier[L]}; match {got == dossier[L]}; "
            f"N_m formula 18*8^m-24*4^m+6*2^m = {18*8**L-24*4**L+6*2**L}; fractions nontriv {cs['f_nontriv']:.4f} traceless {cs['f_traceless']:.4f} -1 {cs['f_minus']:.4f}  ({time.time()-t0:.1f}s, rss {rss_gb():.2f} GB)")
        out[L] = dict(tiles=len(tiles), poses_identical=same_poses, cubes_identical=cubes_ok, box_filled=fills, panels=len(panels),
                      panel_multiset_equal=ms_own == ms_rep, classes=got, dossier=dossier[L], match=got == dossier[L], fractions=[cs['f_nontriv'], cs['f_traceless'], cs['f_minus']])
    say(f" limit fractions: nontriv 17/36 = {17/36:.6f}, traceless 55/144 = {55/144:.6f}, -1 13/144 = {13/144:.6f}")
    # level 5 by re-running the two existing enumerators (same implementations)
    t0 = time.time()
    import phase5a_flux_vs_edge as fe
    tiles5 = tiles_at_level(FR30, 5); owners, hol = fe.plaquettes(tiles5, 5); f5 = fe.flux_fractions(hol)
    say(f" level 5 re-run of phase5a_flux_vs_edge.plaquettes (same implementation): N={f5['N']} +1={f5['n_plus']} -1={f5['n_minus']} traceless={f5['n_traceless']}; "
        f"fractions nontriv {f5['f_nontriv']:.4f} traceless {f5['f_traceless']:.4f} -1 {f5['f_minus']:.4f} (dossier 0.4763/0.3912/0.0851)  ({time.time()-t0:.0f}s)")
    out['level5_flux_vs_edge'] = f5
    t0 = time.time()
    import phase5a_independent_enumerator as ie
    Lv = ie.Level(5); res5 = Lv.plaquettes_vectorised()
    say(f" level 5 re-run of phase5a_independent_enumerator.Level(5).plaquettes_vectorised (same implementation): {res5}  ({time.time()-t0:.0f}s)")
    out['level5_independent_enumerator'] = res5
    dump(out)

def part_bottoms(levels=(2, 3, 4, 5)):
    say, dump = say_factory('bottoms'); out = {}
    say("PHASE V-B / A (b)+(e): pinned bottoms from own assembly + own solver calls; ground-state organisation statistics")
    dossier = {2: 10.776951, 3: 9.378470, 4: 8.919634, 5: 8.797011}
    dossier_ipr = {2: 2.39, 3: 6.42, 4: 9.15, 5: 19.93}
    for L in levels:
        t0 = time.time(); tiles, owner, panels, link = build(L); n = len(tiles)
        H, deg = own_H(tiles, panels, pinned=True, link=link)
        nz, hdef = hermiticity_defect(H); gdef = gaussian_integer_defect(H)
        tb = time.time() - t0; t0 = time.time()
        if L <= 3: lam, V, res = solve_dense(H, 4); how = 'dense eigh (scipy.linalg.eigh)'
        elif L == 4: lam, V, res = solve_shift_invert(H, 4, sigma=8.0); how = 'scipy eigsh shift-invert sigma=8.0 (sparse LU)'
        else: lam, V, res = solve_lobpcg(H, 4, block=6, seed=1, tol=1e-7, maxiter=4000); how = 'scipy lobpcg block 6 seed 1 tol 1e-7 diag precond'
        ts = time.time() - t0
        p1 = tile_density(V[:, 0]); p2 = tile_density(V[:, 1]); p = 0.5 * (p1 + p2)
        masks = interface_masks(n, panels, L); dg = diagnostics(p, L, masks, deg)
        say(f" level {L}: n={n} dim={H.shape[0]} nnz={H.nnz} Hermiticity defect {hdef:.1e} (nonzeros {nz}), Gaussian-integer defect {gdef:.1e}, build {tb:.1f}s")
        say(f"    {how}: lambda_1..4 = {np.round(lam, 9).tolist()}  residuals {['%.1e' % r for r in res]}  Kramers split lambda_2-lambda_1 = {lam[1]-lam[0]:.2e}, next pair gap {lam[2]-lam[0]:.6f}  ({ts:.0f}s, rss {rss_gb():.2f} GB)")
        say(f"    dossier bottom {dossier[L]:.6f}: difference {lam[0]-dossier[L]:+.2e}")
        say(f"    IPR*n = {dg['ipr_n']:.4f} (dossier {dossier_ipr[L]}); pair densities max|p1-p2| = {np.abs(p1-p2).max():.1e}; boundary weight {dg['boundary_weight']:.5f} (boundary fraction {dg['boundary_fraction']:.4f})")
        say(f"    interface weight by depth {{d: w/frac (enrichment)}}: " + '  '.join(f"d{d}: {dg['interface_weight'][d]:.4f}/{dg['interface_fraction'][d]:.4f} ({dg['interface_enrichment'][d]:.2f})" for d in masks))
        say(f"    box counting 1/S2(d): " + '  '.join(f"{dg['inv_S2'][d]:.3f}" for d in masks) + "   D2(d)=log2(S2(d-1)/S2(d)): " + ' '.join(f"{dg['D2_box'][d]:.2f}" for d in masks))
        rec = dict(dim=int(H.shape[0]), nnz=int(H.nnz), hermiticity_defect=hdef, gaussian_defect=gdef, solver=how, lambda_=lam.tolist(), residuals=res.tolist(),
                   kramers_split=float(lam[1] - lam[0]), dossier=dossier[L], diff=float(lam[0] - dossier[L]), seconds=ts, **dg)
        # stored weight file comparison
        wf = os.path.join(RES, f'phase5a_fr30_level{L}_groundstate_weights.npy')
        if os.path.exists(wf):
            w = np.load(wf); dgw = diagnostics(w / w.sum(), L, masks, deg)
            say(f"    stored weight file {os.path.basename(wf)}: IPR*n {dgw['ipr_n']:.4f}, max|p_own - p_stored| = {np.abs(p - w/w.sum()).max():.1e}, L1 = {np.abs(p - w/w.sum()).sum():.1e}; "
                f"stored interface w(1) {dgw['interface_weight'][1]:.4f}, 1/S2(d) " + ' '.join(f"{dgw['inv_S2'][d]:.3f}" for d in masks))
            rec['stored'] = dict(ipr_n=dgw['ipr_n'], max_diff=float(np.abs(p - w / w.sum()).max()), interface_weight=dgw['interface_weight'], inv_S2=dgw['inv_S2'])
        out[L] = rec
    ks = sorted(out)
    say(" monotonicity of pinned bottoms in level: " + ', '.join(f"{out[L]['lambda_'][0]:.6f}" for L in ks) + f"  non-increasing: {all(out[ks[i+1]]['lambda_'][0] <= out[ks[i]]['lambda_'][0] for i in range(len(ks)-1))}")
    say(" two-level D2 = log2(IPR_L / IPR_{L+1}) (linear size doubles per level): " + ', '.join(f"{ks[i]}->{ks[i+1]}: {np.log2(out[ks[i]]['ipr']/out[ks[i+1]]['ipr']):.2f}" for i in range(len(ks) - 1)) + "  (dossier 2.49, 1.88 for 3->4, 4->5)")
    # stored level-6 weight file (read + re-analysed; no level-6 operator is built here)
    wf6 = os.path.join(RES, 'phase5a_fr30_level6_groundstate_weights.npy')
    if os.path.exists(wf6):
        w = np.load(wf6); w = w / w.sum(); n6 = len(w); S2 = [float((w.reshape(8 ** d, 8 ** (6 - d)).sum(axis=1) ** 2).sum()) for d in range(1, 7)]
        say(f" stored level-6 weights (read, re-analysed only; interfaces need the level-6 panel list which is not built here): n={n6}, IPR*n = {(w**2).sum()*n6:.3f} (dossier 42.79), 1/S2(d) = {[round(1/s, 3) for s in S2]}, "
            f"D2 5->6 from stored level-5/6 IPR: {np.log2(out[5]['ipr'] / (w**2).sum()) if 5 in out else float('nan'):.2f} (dossier 1.90)")
        out['level6_stored'] = dict(ipr_n=float((w ** 2).sum() * n6), inv_S2=[1 / s for s in S2])
    dump(out)

def part_periodic():
    say, dump = say_factory('periodic'); out = {}
    say("PHASE V-B / A (c): Lambda_7 chair crystal rebuilt from the definition; own real-space torus operator and own Bloch blocks")
    so3 = so3z_list()
    # crystal sanity
    cr1 = ChairCrystal(np.eye(3, dtype=int)); hops = cr1.hops()
    say(f" k=1: hops per chair = {len(hops)} (24 expected); neighbour displacements {sorted(collections.Counter(tuple(int(x) for x in d) for _,_,d,_ in hops).items())}")
    # natural FR30 bijection on 2L
    cr = ChairCrystal(2 * np.eye(3, dtype=int))
    fr30_frames = [perm_mat(FR30['0'])] + [np.diag([1 - 2 * v[0], 1 - 2 * v[1], 1 - 2 * v[2]]) @ perm_mat(FR30[v]) for v in U3]
    fr30_idx = [next(i for i, g in enumerate(so3) if (g == F).all()) for F in fr30_frames]
    eps = [tuple(int(x) % 2 for x in m) for m in cr.reps]
    nat = [0 if e == (1, 1, 1) else 1 + U3.index(e) for e in eps]
    frames_nat = [fr30_idx[p] for p in nat]
    say(f" cosets of 2L (canonical reps, record order): {[m.tolist() for m in cr.reps]}; natural bijection FR30 frame slots {nat} -> SO3Z indices {frames_nat}")
    t0 = time.time(); rb = cr.bloch_bottom(frames_nat, so3, ngrid=8)
    say(f" natural bijection, own Bloch: E_per = {rb['E']:.9f} at theta={np.round(rb['theta'],5).tolist()} (grid min {rb['grid_min']:.9f}); dossier 10.644234146; diff {rb['E']-10.644234146:+.2e}  ({time.time()-t0:.1f}s)")
    out['natural'] = dict(E_bloch=rb['E'], theta=rb['theta'])
    for N in (2, 4):
        t0 = time.time(); H, npan, plaq = cr.torus(frames_nat, so3, N)
        nz, hd = hermiticity_defect(H)
        if H.shape[0] <= 1200: w = np.linalg.eigvalsh(H.toarray())[:4]
        else: w = np.sort(spl.eigsh(H, k=4, sigma=5.0, which='LM')[0])
        say(f"   own real-space torus N={N}: dim {H.shape[0]}, panels {npan} (=24*8*N^3: {npan==24*8*N**3}), Hermiticity defect {hd:.1e}, lowest {np.round(w,9).tolist()}; "
            f"torus plaquette classes per fundamental domain {dict(plaq)} (record: 1:42 -1:26 i:20 j:32 k:24, 144 inter-tile)  ({time.time()-t0:.1f}s)")
        out['natural'][f'torus_N{N}'] = dict(lowest=w.tolist(), panels=npan, classes=dict(plaq))
    # D2 counterexample record
    S = np.array([[1, 0, 6], [0, 1, 6], [0, 0, 8]]); frames = [2, 2, 10, 10, 7, 6, 16, 10]
    cr8 = ChairCrystal(S)
    say(f" D2 record S={S.tolist()} frames={frames}: coset reps (record order) {[m.tolist() for m in cr8.reps]}")
    t0 = time.time(); rb8 = cr8.bloch_bottom(frames, so3, ngrid=8, nstart=5)
    say(f"   own Bloch: E_per = {rb8['E']:.9f} at theta={np.round(rb8['theta'],5).tolist()} (grid min {rb8['grid_min']:.9f}); dossier 9.633732; diff {rb8['E']-9.633732107:+.2e}  ({time.time()-t0:.1f}s)")
    out['d2'] = dict(E_bloch=rb8['E'], theta=rb8['theta'], grid_min=rb8['grid_min'])
    for N in (4, 8):
        t0 = time.time(); H, npan, plaq = cr8.torus(frames, so3, N); nz, hd = hermiticity_defect(H)
        w = np.sort(spl.eigsh(H, k=4, sigma=5.0, which='LM')[0])
        # commensurate Bloch minimum with own blocks
        th = np.array(list(itertools.product(np.arange(N) / N, repeat=3))); Q = (2 * np.pi * np.linalg.solve(cr8.Bp.astype(float), th.T)).T
        comm = min(np.linalg.eigvalsh(rb8['Hq'](q))[0] for q in Q)
        tot = sum(plaq.values()); trl = plaq['i'] + plaq['j'] + plaq['k']
        say(f"   own real-space torus N={N}: dim {H.shape[0]}, panels {npan}, Hermiticity defect {hd:.1e}, lowest {np.round(w,9).tolist()}; own commensurate Bloch min {comm:.9f} |diff| {abs(w[0]-comm):.1e}; "
            f"lambda_min >= E_per: {w[0] >= rb8['E'] - 1e-9}; torus classes {dict(plaq)} -> nontriv {1-plaq['+1']/tot:.4f} traceless {trl/tot:.4f} -1 {plaq['-1']/tot:.4f} (record 0.5000/0.3750/0.1250; D2 N=8 torus lambda_min 9.697684260)  ({time.time()-t0:.1f}s)")
        out['d2'][f'torus_N{N}'] = dict(lowest=w.tolist(), comm=comm, classes=dict(plaq))
    dump(out)

def part_controls():
    say, dump = say_factory('controls'); out = {}
    say("PHASE V-B / A (d): substitution controls (seeds 1 and 108) at level 4 with own code; flux_vs_edge table re-run from a scratch copy of the JSONs")
    FIT = (-1.904, 14.303, 30.696)
    txt = open(os.path.join(RES, 'phase5a_periodic_control_T.txt')).read()
    say(f" regression constants in audit/results/phase5a_periodic_control_T.txt: 'least-squares E_per ~ -1.904 + 14.303 f_traceless + 30.696 f_-1' present: {'-1.904 + 14.303 f_traceless + 30.696 f_-1' in txt}")
    import phase5a_scaling_controls as sc
    import phase5a_flux_vs_edge as fe
    for seed in (1, 108):
        dec = own_random_decoration(seed); dec_ref, _ = sc.random_decoration(seed)
        same = dec == dec_ref
        rec = json.load(open(os.path.join(RES, f'phase5a_flux_vs_edge_randdec{seed}.json')))
        stored_dec = {k: tuple(v) for k, v in rec['decoration'].items()}
        same_stored = all(tuple(dec[k if k == '0' else tuple(int(x) for x in k.strip('()').split(','))]) == v for k, v in stored_dec.items())
        say(f" seed {seed}: own decoration {dec}; equals scaling_controls.random_decoration: {same}; equals decoration stored in JSON: {same_stored}")
        t0 = time.time(); tiles, owner, panels, link = build(4, dec); n = len(tiles)
        counts, _ = own_plaquettes(tiles, owner, classes_only=True); cs = class_summary(counts)
        H, deg = own_H(tiles, panels, link=link); lam, V, res = solve_shift_invert(H, 4, sigma=5.0)
        p = 0.5 * (tile_density(V[:, 0]) + tile_density(V[:, 1])); masks = interface_masks(n, panels, 4)
        L4 = rec['levels']['4']
        say(f"   level 4 own: E0 = {lam[0]:.6f} (pair {lam[1]:.6f}, residuals {['%.1e' % r for r in res[:2]]}) vs stored {L4['lambda'][0]:.6f} (diff {lam[0]-L4['lambda'][0]:+.1e}); "
            f"IPR*n {float((p**2).sum())*n:.3f} vs stored {L4['ipr_n']:.3f}; interface1 weight {p[masks[1]].sum():.3f} vs stored {L4['interface1_weight']:.3f}  ({time.time()-t0:.0f}s)")
        say(f"   level 4 own flux fractions: nontriv {cs['f_nontriv']:.4f} traceless {cs['f_traceless']:.4f} -1 {cs['f_minus']:.4f} (N={cs['N']}); stored level-5 fractions {rec['flux']['f_nontriv']:.4f}/{rec['flux']['f_traceless']:.4f}/{rec['flux']['f_minus']:.4f}")
        t0 = time.time(); tiles5 = tiles_at_level(dec, 5); owners5, hol5 = fe.plaquettes(tiles5, 5); f5 = fe.flux_fractions(hol5)
        efit = FIT[0] + FIT[1] * f5['f_traceless'] + FIT[2] * f5['f_minus']
        say(f"   level 5 flux via phase5a_flux_vs_edge.plaquettes (re-run): nontriv {f5['f_nontriv']:.4f} traceless {f5['f_traceless']:.4f} -1 {f5['f_minus']:.4f}; equal to stored: {abs(f5['f_nontriv']-rec['flux']['f_nontriv'])<1e-12 and abs(f5['f_minus']-rec['flux']['f_minus'])<1e-12}; "
            f"E_fit recomputed {efit:.3f} vs stored {rec['E_fit']:.3f}; residual r = E0(L5) - E_fit = {rec['levels']['5']['lambda'][0]-efit:+.3f} (table: seed 1 +1.141, seed 108 +2.234)  ({time.time()-t0:.0f}s)")
        out[seed] = dict(decoration={str(k): list(v) for k, v in dec.items()}, same_as_scaling_controls=same, same_as_json=same_stored, E0_L4_own=lam.tolist(), residuals=res.tolist(),
                         E0_L4_stored=L4['lambda'], ipr_n_own=float((p ** 2).sum()) * n, ipr_n_stored=L4['ipr_n'], flux_L4_own=cs, flux_L5_rerun=f5, E_fit=efit, r=rec['levels']['5']['lambda'][0] - efit)
    # table re-run on a scratch copy (the production table() writes into audit/results, which must not be modified)
    import shutil, tempfile
    scratch = tempfile.mkdtemp(prefix='phase5b_a_fluxtable_')
    for fn in os.listdir(RES):
        if fn.startswith('phase5a_flux_vs_edge_') and fn.endswith('.json'): shutil.copy(os.path.join(RES, fn), scratch)
    fe.RES = scratch
    import io, contextlib
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf): fe.table()
    fe.RES = RES
    new = open(os.path.join(scratch, 'phase5a_flux_vs_edge.txt')).read(); old = open(os.path.join(RES, 'phase5a_flux_vs_edge.txt')).read()
    # the stored file has a hand-appended SUPPLEMENT section; compare the generated part
    gen_old = old.split('\nSUPPLEMENT')[0].rstrip('\n'); gen_new = new.rstrip('\n')
    say(f" phase5a_flux_vs_edge.table() re-run on copies of the 19 JSONs (written to {scratch}): generated table identical to the stored file's generated part: {gen_old == gen_new}")
    if gen_old != gen_new:
        import difflib
        for l in list(difflib.unified_diff(gen_old.splitlines(), gen_new.splitlines(), lineterm='', n=0))[:20]: say('   ' + l)
    for l in gen_new.splitlines():
        if l.startswith('fr30') or l.startswith('randdec1 ') or l.startswith('randdec108') or l.startswith('FR30:') or l.startswith('random substitution'): say('   | ' + l)
    out['table_identical'] = gen_old == gen_new
    dump(out)

def part_lowerbound(level=4, full_star_level=5):
    say, dump = say_factory('lowerbound'); out = {}
    say("PHASE V-B / A (f): exact rational LDL^* certificates (own code, real symmetric embedding) and the star-sum lower bound")
    t0 = time.time(); tiles, owner, panels, link = build(level); n = len(tiles)
    edges = all_edges_with_forms(tiles, owner, link)
    sigs = {}
    for sig, cyc, links in edges:
        if sig not in sigs:
            H, labels = plaquette_form(cyc, links); sigs[sig] = H
    lam = {s: float(np.linalg.eigvalsh(H)[0]) for s, H in sigs.items()}
    vals = sorted(set(round(v, 9) for v in lam.values()))
    say(f" T_{level}: {len(edges)} inter-tile lattice edges, {len(sigs)} distinct signatures (pattern + signed links); distinct lambda_min: {vals}")
    say(f"   analytic 2-2cos(theta/l): {sorted(set(round(2-2*np.cos(t/l), 9) for t in (np.pi/2, np.pi) for l in (2,3,4)))}")
    nonflat = [s for s in sigs if lam[s] > 1e-9]; flat = [s for s in sigs if lam[s] <= 1e-9]
    mu = {}; fails = 0; rejects = 0; t1 = time.time()
    for s in nonflat:
        m = Fraction(int(lam[s] * 10 ** 6) - 2, 10 ** 6); A = real_embedding(sigs[s])
        ok = exact_pd(A, m); fails += not ok
        rej = not exact_pd(A, m + Fraction(22, 10 ** 6)); rejects += rej           # must reject lambda_min + 2e-5
        mu[s] = m if ok else Fraction(0)
    for s in flat:
        mu[s] = Fraction(0)
    flat_kind = collections.Counter(exact_min_pivot_sign(real_embedding(sigs[s])) for s in flat)
    say(f"   own exact LDL^T (real embedding, Fractions): {len(nonflat)} non-flat signatures certified h_e - mu_e > 0 with mu_e = (floor(1e6 lambda)-2)/1e6: failures {fails}; "
        f"the same test rejects mu_e + 2.2e-5 for {rejects}/{len(nonflat)}; {len(flat)} flat signatures: exact elimination {dict(flat_kind)}  ({time.time()-t1:.0f}s)")
    out['n_signatures'] = len(sigs); out['n_nonflat'] = len(nonflat); out['failures'] = fails; out['rejects'] = rejects
    # star sums at this level and at full_star_level: S(a) = sum over inter-tile edges touching tile a of mu_e; complete-star tiles only
    def star_sums(L):
        tl, ow, pn, lk = build(L); ed = all_edges_with_forms(tl, ow, lk)
        # complete star: all 26-neighbours of all 7 cubes are present
        NB = [d for d in itertools.product((-1, 0, 1), repeat=3) if d != (0, 0, 0)]
        complete = np.ones(len(tl), bool)
        for a, (_, _, cs) in enumerate(tl):
            for c in cs:
                if not all((c[0]+d[0], c[1]+d[1], c[2]+d[2]) in ow for d in NB): complete[a] = False; break
        S = [Fraction(0)] * len(tl); cnt = np.zeros(len(tl), int); newsig = 0
        for sig, cyc, links in ed:
            if sig not in mu:
                H, _ = plaquette_form(cyc, links); l = float(np.linalg.eigvalsh(H)[0]); newsig += 1
                if l > 1e-9:
                    m = Fraction(int(l * 10 ** 6) - 2, 10 ** 6); assert exact_pd(real_embedding(H), m); mu[sig] = m
                else: mu[sig] = Fraction(0)
            for t in set(cyc): S[t] += mu[sig]; cnt[t] += 1
        Sc = [S[a] for a in range(len(tl)) if complete[a]]
        return dict(n=len(tl), complete=int(complete.sum()), edges_per_complete_tile=sorted(set(int(cnt[a]) for a in range(len(tl)) if complete[a])),
                    min_S=min(Sc), n_distinct_S=len(set(Sc)), new_signatures=newsig)
    for L in sorted(set([level, full_star_level])):
        t1 = time.time(); ss = star_sums(L)
        say(f"   T_{L}: {ss['complete']} tiles with complete vertex stars of {ss['n']}; inter-tile edges per complete tile {ss['edges_per_complete_tile']}; new signatures beyond T_{level}: {ss['new_signatures']}; "
            f"min over complete tiles of sum_e mu_e = {ss['min_S']} = {float(ss['min_S']):.7f} -> E_bulk >= {ss['min_S']/4} = {float(ss['min_S'])/4:.7f} (dossier 3137451/2000000 = 1.5687255; equal: {ss['min_S']/4 == Fraction(3137451, 2000000)}); "
            f"{ss['n_distinct_S']} distinct star sums  ({time.time()-t1:.0f}s)")
        out[f'T{L}'] = {k: (str(v) if isinstance(v, Fraction) else v) for k, v in ss.items()}
    say(f" total {time.time()-t0:.0f}s, rss {rss_gb():.2f} GB")
    dump(out)

if __name__ == '__main__':
    os.environ.setdefault('OMP_NUM_THREADS', '1')
    part = sys.argv[1]
    if part == 'geometry': part_geometry(int(sys.argv[2]) if len(sys.argv) > 2 else 4)
    elif part == 'bottoms': part_bottoms(tuple(int(x) for x in sys.argv[2].split(',')) if len(sys.argv) > 2 else (2, 3, 4, 5))
    elif part == 'periodic': part_periodic()
    elif part == 'controls': part_controls()
    elif part == 'lowerbound': part_lowerbound()
    else: raise SystemExit('unknown part')
