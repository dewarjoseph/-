"""
Phase 5a / Task B2a: MATCHED PERIODIC CONTROL BY EXACT BLOCH THEORY.

A periodic system with the SAME tiles (3D chairs, 7 unit cubes), the SAME coordination (24 shared unit panels per
chair), the SAME Q8 Clifford link rule  C_ab = (sigma . M_a^T n)(sigma . M_b^T n)  on every shared unit panel, but a
PERIODIC frame field: chairs sit at the points of the index-7 lattice Lambda_7 = ker(x+2y+4z mod 7) as pure
translates (src/chair44/periodic_crystal.py), a sublattice L' of index k is chosen, and a frame M in SO(3,Z) is
assigned to each of the k cosets.  The pinned operator H = 24 - A is then L'-periodic and its spectrum is the union
over the Brillouin zone of the spectra of the 2k x 2k Bloch matrices H(q) = 24 - sum_f e^{i q.d_f} C_f.

Everything is computed from the primitives of audit/independent_clifford_q8_audit.py (FR30, perm_mat, clifford_link,
q8label, SIG); nothing is imported from src/.

Run from the repository root (each stage is one computation; records are appended to results/phase5a_periodic_control_records.jsonl):
  python3 -u -I audit/phase5a_periodic_control.py A1      # crystal checks, k=1, k=2 exhaustive, minimiser validation, k=4 random
  python3 -u -I audit/phase5a_periodic_control.py A2 i    # k=4 exhaustive 24^3 frame triples on diagonal sublattice i=0,1,2
  python3 -u -I audit/phase5a_periodic_control.py A3      # k=8: FR30 frames on L/2L (bijections), random decorations, other index-8 sublattices
  python3 -u -I audit/phase5a_periodic_control.py B       # supercell sanity checks for the k=8 FR30-frame decoration
  python3 -u -I audit/phase5a_periodic_control.py C j     # all 8! bijections of the FR30 frames onto L/2L, chunk j=0..3
  python3 -u -I audit/phase5a_periodic_control.py T       # comparison table E_per vs flux from the saved records
  python3 -u -I audit/phase5a_periodic_control.py S       # quaternionic Bloch symmetry proposition: numerical check
"""
import os, sys, time, itertools, collections
for _v in ('OPENBLAS_NUM_THREADS', 'OMP_NUM_THREADS', 'MKL_NUM_THREADS'): os.environ.setdefault(_v, '1')   # tiny matrices: avoid BLAS thread stalls
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
import scipy.optimize as sopt
import scipy.sparse as sps
import scipy.sparse.linalg as spl
from independent_clifford_q8_audit import FR30, U3, perm_mat, clifford_link, q8label, SIG

T0 = time.time()
def log(*a):
    print(*a, flush=True)

# ----------------------------------------------------------------------------------------------------------------
# 1. The Lambda_7 chair crystal
# ----------------------------------------------------------------------------------------------------------------
B = np.array([[1, 1, 1], [2, 1, -1], [-1, 2, 1]], dtype=int)      # rows = basis of Lambda_7 (ambient coordinates)
BinvT = np.linalg.inv(B.T)                                        # ambient -> L-coordinates: m = B^{-T} x
def phi(c): return (c[0] + 2 * c[1] + 4 * c[2]) % 7
UOF = {phi(u): np.array(u, dtype=int) for u in U3}                 # residue -> cube of the chair at 0
def owner_of_cube(c):
    """Lattice point (ambient) of the chair containing unit cube c (lower corner c in Z^3)."""
    c = np.asarray(c, dtype=int); return c - UOF[phi(c)]
def Lcoords(x):
    m = BinvT @ np.asarray(x, dtype=float); mi = np.rint(m).astype(int)
    assert np.allclose(m, mi, atol=1e-9), x
    return mi

def crystal_checks():
    log("=" * 100); log("1. LAMBDA_7 CHAIR CRYSTAL (pure translations)")
    log(f" basis rows b1,b2,b3 = {B.tolist()}  det = {round(np.linalg.det(B))}  phi(b_i) mod 7 = {[phi(b) for b in B]}")
    log(f" phi(U3) = {[phi(u) for u in U3]}  bijective onto Z_7: {sorted(phi(u) for u in U3) == list(range(7))}")
    # direct tiling check on a box: generate all chairs whose lattice point lies in a large range, count coverage
    N = 12
    box = set(itertools.product(range(N), repeat=3))
    # all lattice points whose chair could intersect the box: lattice points of the box's cubes shifted by -U3
    cand = {tuple(np.array(c) - np.array(u)) for c in box for u in U3}
    cand = {x for x in cand if phi(x) == 0}                                   # Lambda_7 = ker phi
    cover = collections.Counter()
    for x in cand:
        for u in U3:
            c = tuple(np.array(x) + np.array(u))
            if c in box: cover[c] += 1
    log(f" direct check: {N}^3 box, {len(cand)} lattice chairs meeting the box, cubes covered exactly once: {sum(1 for c in box if cover[c] == 1)}/{N**3}, "
        f"overlaps: {sum(1 for c in box if cover[c] > 1)}, gaps: {sum(1 for c in box if cover[c] == 0)}")
    # algebraic check: owner_of_cube is the unique chair containing the cube
    ok = all(tuple(np.asarray(c) - owner_of_cube(c)) in set(U3) for c in box)
    log(f" algebraic owner map consistent on the box: {ok}")
    # panel multigraph of one chair
    faces = chair_faces()
    cnt = collections.Counter(tuple(d) for d, n in faces)
    log(f" boundary panels of one chair: {len(faces)} (= 42 - 2*9 internal adjacencies);  distinct neighbour chairs: {len(cnt)}")
    for d, mult in sorted(cnt.items()):
        m = Lcoords(d); norms = collections.Counter(tuple(n) for dd, n in faces if tuple(dd) == d)
        log(f"   neighbour d={d}  (L-coords {m.tolist()})  panels={mult}  normals={dict(norms)}")
    sym = all(cnt[tuple(-np.array(d))] == mult for d, mult in cnt.items())
    log(f" multiplicities symmetric under d -> -d: {sym};  sum of multiplicities = {sum(cnt.values())}")
    # internal plaquettes: lattice edges of Z^3 all of whose 4 surrounding cubes lie in the same chair
    internal = 0
    for c in box:
        for (i, j) in [(0, 1), (1, 2), (0, 2)]:
            ei = np.eye(3, dtype=int)[i]; ej = np.eye(3, dtype=int)[j]
            o = {tuple(owner_of_cube(np.array(c) + s)) for s in (0 * ei, ei, ei + ej, ej)}
            if len(o) == 1: internal += 1
    log(f" plaquettes (lattice edges) per chair: 21; internal to one chair: {internal / (N**3 / 7):.4f} per chair (expect 3);"
        f" inter-tile: {21 - internal / (N**3 / 7):.4f} per chair (FR30 limit: 18)")
    return faces

def chair_faces():
    """The 24 boundary panels of the chair at the origin: list of (d, n) with d the ambient lattice vector to the
    neighbouring chair and n the outward unit normal (ambient, from this chair to the neighbour)."""
    faces = []
    for u in U3:
        for ax in range(3):
            for s in (1, -1):
                w = np.array(u, dtype=int); w[ax] += s
                if tuple(w) in set(U3): continue
                d = owner_of_cube(w); n = np.zeros(3, dtype=int); n[ax] = s
                faces.append((d, n))
    assert len(faces) == 24
    return faces
FACES = chair_faces()
FACES_M = [Lcoords(d) for d, n in FACES]                          # neighbour displacement in L-coordinates

# ----------------------------------------------------------------------------------------------------------------
# 2. Frames, sublattices, decorations
# ----------------------------------------------------------------------------------------------------------------
SO3Z = [np.diag(s) @ perm_mat(p) for p in itertools.permutations(range(3)) for s in itertools.product((1, -1), repeat=3)]
SO3Z = [g for g in SO3Z if round(np.linalg.det(g)) == 1]
assert len(SO3Z) == 24
SO3Z_INDEX = {tuple(g.flatten()): i for i, g in enumerate(SO3Z)}
def redec(rec): return Decoration(np.array(rec['S']), [SO3Z[i] for i in rec['frames']])
FR30_FRAMES = [perm_mat(FR30['0'])] + [np.diag([1 - 2 * v[0], 1 - 2 * v[1], 1 - 2 * v[2]]) @ perm_mat(FR30[v]) for v in U3]
FR30_LABELS = ['centre'] + [str(v) for v in U3]

def hnf_sublattices(k):
    """All sublattices of index k of Z^3 (in L-coordinates), as integer 3x3 matrices S whose ROWS span L'
    (Hermite normal form, upper triangular, 0 <= S[i,j] < S[j,j] for i<j)."""
    out = []
    for d1 in range(1, k + 1):
        if k % d1: continue
        for d2 in range(1, k // d1 + 1):
            if (k // d1) % d2: continue
            d3 = k // (d1 * d2)
            for a in range(d2):
                for b in range(d3):
                    for c in range(d3):
                        out.append(np.array([[d1, a, b], [0, d2, c], [0, 0, d3]], dtype=int))
    return out

class Decoration:
    """Periodic frame field: sublattice S (rows = L'-basis in L-coords, det k) and a frame per coset."""
    def __init__(self, S, frames):
        self.S = np.asarray(S, dtype=int); self.k = int(round(np.linalg.det(self.S)))
        self.adjT = np.rint(self.k * np.linalg.inv(self.S)).astype(int).T          # adjT @ S^T = k I
        assert (self.adjT @ self.S.T == self.k * np.eye(3, dtype=int)).all()
        # enumerate cosets of L' in L by scanning a box of L-coordinates
        keys = {}
        for m in itertools.product(range(0, self.k), repeat=3):
            key = self.key(np.array(m))
            if key not in keys: keys[key] = np.array(m)
            if len(keys) == self.k: break
        assert len(keys) == self.k, (len(keys), self.k)
        self.keys = sorted(keys); self.index = {key: i for i, key in enumerate(self.keys)}
        self.reps = [keys[key] for key in self.keys]                               # representative m per coset
        assert len(frames) == self.k
        self.frames = [np.asarray(f, dtype=int) for f in frames]
        self.Bp = self.S @ B                                                       # rows = L'-basis, ambient
        self.BpinvT = np.linalg.inv(self.Bp.T)
        self._hops = None
    def key(self, m): return tuple((self.adjT @ m) % self.k)
    def coset(self, m): return self.index[self.key(np.asarray(m, dtype=int))]
    def hops(self):
        """List of (c, c', d_ambient, C) over all cosets c and all 24 panels of the representative chair."""
        if self._hops is None:
            H = []
            for c, m in enumerate(self.reps):
                for (d, n), md in zip(FACES, FACES_M):
                    c2 = self.coset(m + md)
                    C = clifford_link(self.frames[c], self.frames[c2], n)
                    H.append((c, c2, d, C))
            self._hops = H
            k = self.k; F = len(H)
            E = np.zeros((F, 2 * k, 2 * k), dtype=complex); D = np.zeros((F, 3))
            for f, (c, c2, d, C) in enumerate(H):
                E[f, 2 * c:2 * c + 2, 2 * c2:2 * c2 + 2] = C; D[f] = d
            self._E = E.reshape(F, -1); self._D = D
        return self._hops
    def Hq(self, q):
        """Bloch matrix at ambient wave-vector q (shape (2k,2k))."""
        self.hops(); ph = np.exp(1j * (self._D @ np.asarray(q, dtype=float)))
        A = (ph @ self._E).reshape(2 * self.k, 2 * self.k)
        return 24.0 * np.eye(2 * self.k) - A
    def Hq_batch(self, Q):
        self.hops(); ph = np.exp(1j * (Q @ self._D.T))                    # (Nq, F)
        A = (ph @ self._E).reshape(len(Q), 2 * self.k, 2 * self.k)
        return 24.0 * np.eye(2 * self.k)[None] - A
    def q_of_theta(self, th):
        """theta in [0,1)^3 (reduced coordinates of the BZ of L') -> ambient q."""
        return 2 * np.pi * np.linalg.solve(self.Bp.astype(float), np.asarray(th, dtype=float))
    def theta_of_q(self, q): return (self.Bp @ np.asarray(q) / (2 * np.pi)) % 1.0
    def lowest(self, q):
        return np.linalg.eigvalsh(self.Hq(q))[0]
    # ------------- exact flux statistics on the torus Z^3 / L' -------------
    def flux(self):
        """Q8 class counts of all lattice-edge plaquettes of the torus Z^3/L' (7k cubes, 21k plaquettes), split into
        inter-tile (not all four cubes in one chair) and internal."""
        k = self.k
        # fundamental domain of Z^3 / (L' acting by translation): all cubes of the k chairs at the representatives
        cubes = [B.T @ m + np.array(u) for m in self.reps for u in U3]
        assert len(cubes) == 7 * k
        def frame_of(c):
            x = owner_of_cube(c); return self.frames[self.coset(Lcoords(x))], tuple(x)
        cls = collections.Counter(); internal = 0; ntot = 0
        for c in cubes:
            for (i, j) in [(0, 1), (1, 2), (0, 2)]:
                ei = np.eye(3, dtype=int)[i]; ej = np.eye(3, dtype=int)[j]
                ring = [c, c + ei, c + ei + ej, c + ej]
                fr = [frame_of(cc) for cc in ring]
                ntot += 1
                if len({o for _, o in fr}) == 1: internal += 1; continue
                W = np.eye(2, dtype=complex)
                for t in range(4):
                    (Ma, oa), (Mb, ob) = fr[t], fr[(t + 1) % 4]
                    if oa == ob: continue
                    n = ring[(t + 1) % 4] - ring[t]
                    W = W @ clifford_link(Ma, Mb, n)
                cls[q8label(W)] += 1
        assert ntot == 21 * k and internal == 3 * k, (ntot, internal, k)
        inter = ntot - internal
        byclass = {'1': cls['+1'], '-1': cls['-1'], 'i': cls['+i'] + cls['-i'], 'j': cls['+j'] + cls['-j'], 'k': cls['+k'] + cls['-k']}
        assert sum(byclass.values()) == inter and cls['other'] == 0
        return inter, byclass

def band_minimum(dec, ngrid=8, nstart=3, gtol=1e-9):
    """Lowest band: coarse grid over the BZ of L' (ngrid^3 points incl. all TRIMs when ngrid even), then BFGS
    refinement in ambient q from the best nstart grid points, using the Hellmann-Feynman gradient
    dE/dq_i = <v0| dH/dq_i |v0> (for an exactly degenerate smooth band any vector of the eigenspace gives the same
    gradient; an accidental crossing at the minimum would show up as a BFGS failure, in which case the best grid /
    line-search value is kept).  Returns dict."""
    dec.hops(); D = dec._D; E3 = dec._E.reshape(-1, 2 * dec.k, 2 * dec.k)
    th = np.array(list(itertools.product(np.arange(ngrid) / ngrid, repeat=3)))
    Q = (2 * np.pi * np.linalg.solve(dec.Bp.astype(float), th.T)).T
    ev = np.linalg.eigvalsh(dec.Hq_batch(Q))
    e0 = ev[:, 0]; order = np.argsort(e0)
    def fg(q):
        w, V = np.linalg.eigh(dec.Hq(q)); v0 = V[:, 0]
        ph = np.exp(1j * (D @ q)); M = np.einsum('a,fab,b->f', v0.conj(), E3, v0)        # <v0|E_f|v0>
        g = -np.real((1j * ph * M) @ D)                                                    # d/dq_i of -sum_f e^{iq.d_f} <E_f>
        return w[0], g
    minima = []
    for s in order[:nstart]:
        r = sopt.minimize(fg, Q[s], jac=True, method='BFGS', options=dict(gtol=gtol, maxiter=300))
        E, qq = (r.fun, r.x) if r.fun <= e0[s] + 1e-12 else (e0[s], Q[s])
        minima.append((E, qq))
    minima.sort(key=lambda t: t[0]); E, q = minima[0]
    w = np.linalg.eigvalsh(dec.Hq(q))
    thm = dec.theta_of_q(q)
    trim = all(min(abs(t), abs(t - 0.5), abs(t - 1)) < 2e-4 for t in thm)
    gamma = all(min(abs(t), abs(t - 1)) < 2e-4 for t in thm)
    distinct = []
    for e, qq in minima:
        if e - E < 1e-7:
            t = dec.theta_of_q(qq)
            if not any(np.linalg.norm((t - t2 + 0.5) % 1 - 0.5) < 1e-3 for t2 in distinct): distinct.append(t)
    # degeneracy of the lowest band at a generic point (minimum + fixed offset)
    wg = np.linalg.eigvalsh(dec.Hq(q + np.array([0.37, -0.21, 0.52])))
    return dict(E=E, q=q, theta=thm, gap12=w[1] - w[0], gap13=(w[2] - w[0]) if len(w) > 2 else float('nan'), trim=trim, gamma=gamma,
                grid_min=e0.min(), grid_max_band0=e0.max(), n_distinct_minima=len(distinct), ev_at_min=w[:4], gap12_generic=wg[1] - wg[0])

def hessian_fd(dec, q, h):
    f = lambda qq: np.linalg.eigvalsh(dec.Hq(qq))[0]
    e = np.eye(3); H = np.zeros((3, 3)); f0 = f(q)
    for i in range(3):
        H[i, i] = (f(q + h * e[i]) - 2 * f0 + f(q - h * e[i])) / h ** 2
        for j in range(i + 1, 3):
            H[i, j] = H[j, i] = (f(q + h * e[i] + h * e[j]) - f(q + h * e[i] - h * e[j]) - f(q - h * e[i] + h * e[j]) + f(q - h * e[i] - h * e[j])) / (4 * h ** 2)
    return H

def hessian_pt(dec, q, degtol=1e-8):
    """Second-order (degenerate) perturbation theory for the lowest band at q.  Let P be the eigenspace of the
    lowest eigenvalue (dimension g = 1 or 2).  The effective quadratic form is the g x g matrix
      K_ij = P d2H_ij P + 2 Re sum_{n notin P} P dH_i |n><n| dH_j P / (E0 - E_n).
    Returns (K as a (3,3,g,g) array, first-order g x g matrices, g).  When the band stays exactly degenerate
    the g x g blocks are scalar multiples of the identity and the Hessian is well defined."""
    dec.hops(); D = dec._D; k = dec.k
    ph = np.exp(1j * (D @ q))
    H0 = dec.Hq(q); w, V = np.linalg.eigh(H0)
    g = int(np.sum(w - w[0] < degtol)); P = V[:, :g]; E0 = w[0]; R = V[:, g:]; wr = w[g:]
    dH = [-((1j * D[:, i] * ph) @ dec._E).reshape(2 * k, 2 * k) for i in range(3)]
    d2H = [[-((-D[:, i] * D[:, j] * ph) @ dec._E).reshape(2 * k, 2 * k) for j in range(3)] for i in range(3)]
    grad = np.array([P.conj().T @ dH[i] @ P for i in range(3)])
    K = np.zeros((3, 3, g, g), dtype=complex)
    for i in range(3):
        Ai = P.conj().T @ dH[i] @ R                                   # (g, 2k-g)
        for j in range(3):
            Aj = P.conj().T @ dH[j] @ R
            K[i, j] = P.conj().T @ d2H[i][j] @ P + (Ai / (E0 - wr)[None, :]) @ Aj.conj().T + ((Aj / (E0 - wr)[None, :]) @ Ai.conj().T)
    return K, grad, g

def effective_mass_report(dec, q, gap12):
    out = {}
    hs = {h: hessian_fd(dec, q, h) for h in (0.08, 0.04, 0.02, 0.01)}
    out['fd'] = hs
    # Richardson extrapolation removes the O(h^2) error of central differences; convergence = change between
    # the extrapolants built from (0.04,0.02) and (0.02,0.01)
    R1 = (4 * hs[0.02] - hs[0.04]) / 3; R2 = (4 * hs[0.01] - hs[0.02]) / 3
    out['fd_R'] = R2; out['fd_conv'] = np.max(np.abs(R2 - R1)); out['fd_raw_conv'] = np.max(np.abs(hs[0.02] - hs[0.01]))
    K, grad, g = hessian_pt(dec, q)
    out['pt_g'] = g
    if g == 1:
        out['pt'] = np.real(K[:, :, 0, 0]); out['grad'] = np.real(grad[:, 0, 0])
    else:
        # scalar part and the maximal deviation from scalar (non-scalar => the two bands split at second order)
        scal = np.real(np.einsum('ijaa->ij', K)) / g
        dev = max(np.max(np.abs(K[i, j] - scal[i, j] * np.eye(g))) for i in range(3) for j in range(3))
        out['pt'] = scal; out['pt_nonscalar'] = dev; out['grad'] = np.array([np.max(np.abs(grad[i])) for i in range(3)])
    return out

def fmt_mat(M): return "[" + "; ".join(" ".join(f"{x:+.5f}" for x in row) for row in M) + "]"

def analyse(dec, label, ngrid=8, full=True):
    r = band_minimum(dec, ngrid=ngrid)
    inter, cls = dec.flux()
    fnt = 1 - cls['1'] / inter; ftr = (cls['i'] + cls['j'] + cls['k']) / inter; fm1 = cls['-1'] / inter
    rec = dict(label=label, k=dec.k, E=r['E'], theta=r['theta'], trim=r['trim'], gamma=r['gamma'], gap12=r['gap12'],
               gap13=r['gap13'], ndist=r['n_distinct_minima'], gap12_generic=r['gap12_generic'], f_nontriv=fnt, f_traceless=ftr, f_minus1=fm1, cls=cls, inter=inter,
               S=dec.S.tolist(), frames=[SO3Z_INDEX[tuple(f.flatten())] for f in dec.frames])
    if full:
        em = effective_mass_report(dec, r['q'], r['gap12'])
        rec['hess'] = em['fd_R']; rec['hess_conv'] = em['fd_conv']; rec['hess_raw_conv'] = em['fd_raw_conv']
        rec['hess_eigs'] = np.linalg.eigvalsh(em['fd_R'])
        rec['hess_pt'] = em['pt']; rec['grad_pt'] = em['grad']; rec['pt_g'] = em['pt_g']; rec['pt_nonscalar'] = em.get('pt_nonscalar', 0.0)
    return rec

def print_rec(rec, verbose=True):
    where = 'Gamma' if rec['gamma'] else ('TRIM' if rec['trim'] else 'generic')
    log(f" {rec['label']:48s} k={rec['k']:2d}  E_per={rec['E']:.9f}  theta_min={np.round(rec['theta'], 4).tolist()} ({where})"
        f"  gap12={rec['gap12']:.1e} (generic q: {rec['gap12_generic']:.1e}) gap13={rec['gap13']:.3e}  distinct_minima={rec['ndist']}"
        f"  flux: nontriv={rec['f_nontriv']:.4f} traceless={rec['f_traceless']:.4f} -1={rec['f_minus1']:.4f}  classes={rec['cls']} (inter-tile plaquettes={rec['inter']})")
    if verbose and 'hess' in rec:
        log(f"      Hessian (Richardson FD, h=0.02/0.01) = {fmt_mat(rec['hess'])}  eigs={np.round(rec['hess_eigs'], 5).tolist()}  Richardson change={rec['hess_conv']:.1e} raw |FD(0.02)-FD(0.01)|={rec['hess_raw_conv']:.1e}")
        if 'hess_pt' in rec:
            log(f"      Hessian (2nd-order PT, degeneracy g={rec['pt_g']}, non-scalar part {rec['pt_nonscalar']:.1e}) = {fmt_mat(rec['hess_pt'])}  max|PT-FD|={np.max(np.abs(rec['hess_pt'] - rec['hess'])):.1e}  |grad|={np.linalg.norm(rec['grad_pt']):.1e}")

# ----------------------------------------------------------------------------------------------------------------
# 3. Stages
# ----------------------------------------------------------------------------------------------------------------
FR30_REF = dict(E6=8.77013, E5=8.79701, nontriv=17 / 36, traceless=55 / 144, minus1=13 / 144)

REC_FILE = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'results', 'phase5a_periodic_control_records.jsonl')
def save_records(records, stage=''):
    import json
    keys = ('label', 'k', 'E', 'trim', 'gamma', 'gap12', 'gap12_generic', 'ndist', 'f_nontriv', 'f_traceless', 'f_minus1', 'cls', 'inter', 'S', 'frames', 'hess_conv', 'pt_g', 'pt_nonscalar')
    with open(REC_FILE.replace('.jsonl', f'{stage}.jsonl'), 'a') as f:
        for r in records:
            d = {k: r[k] for k in keys if k in r}; d['theta'] = [float(x) for x in r['theta']]
            if 'hess_eigs' in r: d['hess_eigs'] = [float(x) for x in r['hess_eigs']]; d['hess'] = np.asarray(r['hess']).tolist()
            f.write(json.dumps(d, default=lambda o: float(o) if isinstance(o, (np.floating, np.integer)) else str(o)) + '\n')
def load_records():
    import json, glob
    out = []
    for fn in sorted(glob.glob(REC_FILE.replace('.jsonl', '*.jsonl'))):
        with open(fn) as f: out += [json.loads(l) for l in f if l.strip()]
    return out

def natural_bijection(dec0):
    eps_of = lambda i: tuple(int(x) % 2 for x in dec0.reps[i])              # coset of 2L <-> m mod 2 in {0,1}^3
    return [0 if eps_of(i) == (1, 1, 1) else 1 + U3.index(eps_of(i)) for i in range(8)], eps_of

def stage_A1():
    rng = np.random.default_rng(2026)
    crystal_checks()
    records = []
    log("\n" + "=" * 100); log("2. k=1: ALL FRAMES EQUAL")
    for M in (np.eye(3, dtype=int), SO3Z[5]):
        dec = Decoration(np.eye(3, dtype=int), [M])
        links = collections.Counter(q8label(C) for _, _, _, C in dec.hops())
        rec = analyse(dec, f"k=1 frame={M.tolist()}"); print_rec(rec); records.append(rec)
        log(f"      link values: {dict(links)}  (C_ab=(sigma.u)^2=I for equal frames: trivial connection, E_per=0 at Gamma)")
    K0 = sum(np.outer(d, d) for d, n in FACES).astype(float)
    log(f"      trivial-connection Hessian at Gamma (analytic sum_f d_f d_f^T) = {fmt_mat(K0)}  eigs={np.round(np.linalg.eigvalsh(K0), 5).tolist()}")

    log("\n" + "=" * 100); log("3. k=2: ALL 7 INDEX-2 SUBLATTICES x ALL 24 FRAMES ON THE SECOND COSET (M_0 = I; a common right factor is a global gauge transformation)")
    best2 = []
    for si, S in enumerate(hnf_sublattices(2)):
        for gi, M in enumerate(SO3Z):
            dec = Decoration(S, [np.eye(3, dtype=int), M])
            rec = analyse(dec, f"k=2 S={S.tolist()} M1=#{gi}", full=False); records.append(rec); best2.append(rec)
    seen = {}
    for rec in best2:
        key = (round(rec['E'], 6), round(rec['f_nontriv'], 6), round(rec['f_traceless'], 6), round(rec['f_minus1'], 6))
        seen.setdefault(key, []).append(rec)
    log(f" {len(best2)} decorations, {len(seen)} distinct (E_per, flux) outcomes:")
    for key in sorted(seen):
        recs = seen[key]; rec = recs[0]
        where = 'Gamma' if rec['gamma'] else ('TRIM' if rec['trim'] else 'generic')
        log(f"   E_per={key[0]:.6f}  nontriv={key[1]:.4f} traceless={key[2]:.4f} -1={key[3]:.4f}  x{len(recs):3d}  e.g. {rec['label']}  theta={np.round(rec['theta'],4).tolist()} ({where}) gap12={rec['gap12']:.1e}")
    top = max(best2, key=lambda r: r['E']); rec = analyse(redec(top), top['label'] + " [max E, full]"); print_rec(rec); records.append(rec)

    log("\n" + "=" * 100); log("4a. k=4: 35 INDEX-4 SUBLATTICES, 40 random frame triples each (exhaustive scans of three diagonal sublattices: stage A2)")
    subs4 = hnf_sublattices(4); log(f" number of index-4 sublattices (HNF count): {len(subs4)}")
    mism = 0; worst = 0.0
    for t in range(150):
        S = subs4[rng.integers(len(subs4))]; dec = Decoration(S, [np.eye(3, dtype=int)] + [SO3Z[g] for g in rng.integers(0, 24, 3)])
        e_c = band_minimum(dec, ngrid=4, nstart=2)['E']; e_f = band_minimum(dec, ngrid=8, nstart=3)['E']
        worst = max(worst, abs(e_c - e_f)); mism += abs(e_c - e_f) > 1e-7
    log(f" coarse (4^3 grid, 2 starts) vs fine (8^3 grid, 3 starts) band bottom on 150 random k=4 decorations: mismatches(>1e-7)={mism}, worst |diff|={worst:.2e}")
    mism = 0; worst = 0.0; S8 = 2 * np.eye(3, dtype=int)
    for t in range(60):
        dec = Decoration(S8, [np.eye(3, dtype=int)] + [SO3Z[g] for g in rng.integers(0, 24, 7)])
        e_c = band_minimum(dec, ngrid=4, nstart=2)['E']; e_f = band_minimum(dec, ngrid=8, nstart=3)['E']
        worst = max(worst, abs(e_c - e_f)); mism += abs(e_c - e_f) > 1e-7
    log(f" same test on 60 random k=8 (2L) decorations: mismatches(>1e-7)={mism}, worst |diff|={worst:.2e}")
    tA = time.time(); k4 = []
    for S in subs4:
        for t in range(40):
            tri = tuple(int(x) for x in rng.integers(0, 24, 3))
            dec = Decoration(S, [np.eye(3, dtype=int)] + [SO3Z[g] for g in tri])
            rec = analyse(dec, f"k=4 S={S.tolist()} tri={tri}", full=False); records.append(rec); k4.append(rec)
    Es = np.array([r['E'] for r in k4])
    log(f" 1400 random k=4 decorations: E_per min={Es.min():.5f} max={Es.max():.5f} mean={Es.mean():.4f} median={np.median(Es):.4f}  fraction >=8.77: {np.mean(Es >= 8.77):.4f}  ({time.time()-tA:.0f}s)")
    for r in sorted(k4, key=lambda r: r['E'])[-3:]:
        rec = analyse(redec(r), r['label'] + " [top]"); print_rec(rec); records.append(rec)
    # minimum-location statistics by quotient type
    for name, cond in (("2L subset L' (quotient Z2^a)", True), ("2L not subset L'", False)):
        rs = [r for r in k4 if (np.allclose(np.linalg.solve(np.array(r['S']).T, 2 * np.eye(3)), np.rint(np.linalg.solve(np.array(r['S']).T, 2 * np.eye(3))))) == cond]
        if rs: log(f"   {name}: n={len(rs)}  at Gamma {sum(r['gamma'] for r in rs)}, other TRIM {sum(r['trim'] and not r['gamma'] for r in rs)}, generic {sum(not r['trim'] for r in rs)};  lowest band degenerate at generic q (gap12<1e-9): {sum(r['gap12_generic'] < 1e-9 for r in rs)}")
    save_records(records); log(f"[stage A1 done in {time.time()-T0:.0f}s; {len(records)} records saved]")

EXH = [[2, 2, 1], [1, 1, 4], [4, 1, 1]]
def stage_A2(i):
    rng = np.random.default_rng(100 + i)
    S = np.diag(EXH[i]); log("=" * 100); log(f"4b. k=4 EXHAUSTIVE: sublattice S=diag{EXH[i]} (L/L' = {'Z2xZ2' if EXH[i]==[2,2,1] else 'Z4'}), all 24^3 = 13824 frame triples (M_0 = I), coarse minimiser + exact flux")
    records = []; tA = time.time()
    for tri in itertools.product(range(24), repeat=3):
        dec = Decoration(S, [np.eye(3, dtype=int)] + [SO3Z[g] for g in tri])
        rec = analyse(dec, f"k=4 S={S.tolist()} tri={tri} [exh]", ngrid=4, full=False); records.append(rec)
    Es = np.array([r['E'] for r in records])
    log(f" E_per: min={Es.min():.6f} max={Es.max():.6f} mean={Es.mean():.4f} median={np.median(Es):.4f}  fraction >=8.0: {np.mean(Es >= 8.0):.4f}  >=8.77: {np.mean(Es >= 8.77):.4f}   ({time.time()-tA:.0f}s)")
    hist, edges = np.histogram(Es, bins=np.arange(0, 14.01, 1.0))
    log(" histogram of E_per (unit bins): " + ", ".join(f"[{lo:.0f},{hi:.0f}):{h}" for h, lo, hi in zip(hist, edges[:-1], edges[1:])))
    f = np.array([r['f_nontriv'] for r in records])
    log(" E_per by non-trivial plaquette fraction:")
    for fv in sorted(set(np.round(f, 6))):
        sel = np.abs(f - fv) < 1e-6; log(f"   f_nontriv={fv:.4f}: n={sel.sum():5d}  E_per min={Es[sel].min():.4f} median={np.median(Es[sel]):.4f} max={Es[sel].max():.4f}")
    for j in np.argsort(Es)[-3:]:
        rec = analyse(redec(records[j]), records[j]['label'] + " [top, full]"); print_rec(rec); records.append(rec)
    save_records(records, f'_A2_{i}'); log(f"[stage A2 {i} done in {time.time()-T0:.0f}s; {len(records)} records saved]")

def stage_A3():
    rng = np.random.default_rng(2027); records = []
    log("=" * 100); log("5. k=8, L'=2L: THE EIGHT FR30 LEVEL-1 CHILD FRAMES ON THE EIGHT COSETS")
    S8 = 2 * np.eye(3, dtype=int)
    dec0 = Decoration(S8, [np.eye(3, dtype=int)] * 8)
    nat, eps_of = natural_bijection(dec0)
    log(f" cosets of 2L: keys={dec0.keys}; representatives m={[r.tolist() for r in dec0.reps]}")
    log(f" FR30 level-1 frames: " + "; ".join(f"{l}:{f.tolist()}" for l, f in zip(FR30_LABELS, FR30_FRAMES)))
    log(f" natural bijection (coset eps = m mod 2 -> FR30 child labelled v = eps, centre on eps=(1,1,1)): {[(eps_of(i), FR30_LABELS[nat[i]]) for i in range(8)]}")
    fb = lambda perm: [FR30_FRAMES[p] for p in perm]
    rec = analyse(Decoration(S8, fb(nat)), f"k=8 2L FR30 natural bijection {nat}"); print_rec(rec); records.append(rec)
    alt = list(nat); i0 = nat.index(0); i1 = nat.index(1); alt[i0], alt[i1] = alt[i1], alt[i0]
    rec = analyse(Decoration(S8, fb(alt)), f"k=8 2L FR30 centre<->(0,0,0) swapped {alt}"); print_rec(rec, verbose=False); records.append(rec)
    tB = time.time(); bij = []
    for t in range(400):
        perm = [int(x) for x in rng.permutation(8)]
        r = analyse(Decoration(S8, fb(perm)), f"k=8 2L FR30 bijection {perm}", full=False); bij.append(r); records.append(r)
    Es = np.array([r['E'] for r in bij])
    log(f" 400 random bijections of the FR30 frames onto L/2L: E_per min={Es.min():.6f} max={Es.max():.6f} mean={Es.mean():.4f} sd={Es.std():.4f}"
        f"  nontriv fraction range [{min(r['f_nontriv'] for r in bij):.4f},{max(r['f_nontriv'] for r in bij):.4f}]  fraction >=8.77: {np.mean(Es >= 8.77):.3f}  ({time.time()-tB:.0f}s)")
    for r in sorted(bij, key=lambda r: r['E'])[-3:]:
        rec = analyse(redec(r), r['label'] + " [top]"); print_rec(rec); records.append(rec)
    for r in sorted(bij, key=lambda r: r['E'])[:1]:
        rec = analyse(redec(r), r['label'] + " [bottom]"); print_rec(rec); records.append(rec)

    log("\n" + "=" * 100); log("6. k=8, L'=2L: 600 RANDOM SO(3,Z) FRAME ASSIGNMENTS (M_0 = I);  k=8 OTHER INDEX-8 SUBLATTICES: 155 x 4 random assignments")
    tC = time.time(); rnd8 = []
    for t in range(600):
        fr = [np.eye(3, dtype=int)] + [SO3Z[g] for g in rng.integers(0, 24, 7)]
        r = analyse(Decoration(S8, fr), f"k=8 2L random#{t}", full=False); rnd8.append(r); records.append(r)
    Es = np.array([r['E'] for r in rnd8])
    log(f" 600 random decorations of L/2L: E_per min={Es.min():.6f} max={Es.max():.6f} mean={Es.mean():.4f} sd={Es.std():.4f} "
        f"fraction >=8.77: {np.mean(Es >= 8.77):.4f}  ({time.time()-tC:.0f}s)")
    for r in sorted(rnd8, key=lambda r: r['E'])[-2:]:
        rec = analyse(redec(r), r['label'] + f" frames={r['frames']} [top]"); print_rec(rec); records.append(rec)
    subs8 = hnf_sublattices(8); log(f" number of index-8 sublattices (HNF count): {len(subs8)}")
    oth8 = []
    for S in subs8:
        for t in range(4):
            fr = [np.eye(3, dtype=int)] + [SO3Z[g] for g in rng.integers(0, 24, 7)]
            r = analyse(Decoration(S, fr), f"k=8 S={S.tolist()} random#{t}", full=False); oth8.append(r); records.append(r)
    Es = np.array([r['E'] for r in oth8])
    for r in sorted(oth8, key=lambda r: r['E'])[-2:]:
        rec = analyse(redec(r), r['label'] + f" frames={r['frames']} [top]"); print_rec(rec); records.append(rec)
    log(f" 620 random decorations over all index-8 sublattices: E_per min={Es.min():.6f} max={Es.max():.6f} mean={Es.mean():.4f} sd={Es.std():.4f} "
        f"fraction >=8.77: {np.mean(Es >= 8.77):.4f}  ({time.time()-tC:.0f}s)")
    for name, cond in (("2L subset L' (quotient Z2^a)", True), ("2L not subset L'", False)):
        rs = [r for r in oth8 if (np.allclose(np.linalg.solve(np.array(r['S']).T, 2 * np.eye(3)), np.rint(np.linalg.solve(np.array(r['S']).T, 2 * np.eye(3))))) == cond]
        if rs: log(f"   {name}: n={len(rs)}  at Gamma {sum(r['gamma'] for r in rs)}, other TRIM {sum(r['trim'] and not r['gamma'] for r in rs)}, generic {sum(not r['trim'] for r in rs)};  degenerate at generic q: {sum(r['gap12_generic'] < 1e-9 for r in rs)}")
    save_records(records, '_A3'); log(f"[stage A3 done in {time.time()-T0:.0f}s; {len(records)} records saved]")

def stage_T():
    allr = load_records()
    log("=" * 100); log("7. COMPARISON: E_per versus flux density over ALL periodic decorations analysed (stages A1, A2, A3);  FR30 aperiodic reference marked")
    log(f" FR30 (aperiodic, pinned finite patches, upper bounds on E_bulk): level 5: {FR30_REF['E5']}, level 6: {FR30_REF['E6']};"
        f" flux: nontriv=17/36={FR30_REF['nontriv']:.4f} traceless=55/144={FR30_REF['traceless']:.4f} -1=13/144={FR30_REF['minus1']:.4f}")
    # drop duplicate full re-analyses of the same decoration
    seen = set(); uniq = []
    for r in allr:
        key = (tuple(map(tuple, r['S'])), tuple(r['frames']))
        if key in seen: continue
        seen.add(key); uniq.append(r)
    allr = uniq
    Emax = max(r['E'] for r in allr)
    log(f" distinct periodic decorations: {len(allr)} (k=2: {sum(r['k']==2 for r in allr)}, k=4: {sum(r['k']==4 for r in allr)}, k=8: {sum(r['k']==8 for r in allr)});  global E_per max = {Emax:.6f}  e.g. {[r['label'] for r in allr if r['E'] >= Emax - 1e-9][:2]}")
    log(f" fraction of decorations with E_per >= 8.770: {np.mean([r['E'] >= 8.770 for r in allr]):.4f};  with E_per in [8.5, 9.0]: {np.mean([8.5 <= r['E'] <= 9.0 for r in allr]):.4f}")
    log(" binned by non-trivial plaquette fraction f_nontriv (inter-tile plaquettes):")
    bins = np.linspace(0, 1, 21)
    for lo, hi in zip(bins[:-1], bins[1:]):
        rs = [r for r in allr if lo <= r['f_nontriv'] < hi + (1e-12 if hi == 1 else 0)]
        if not rs: continue
        Es = np.array([r['E'] for r in rs]); mark = "  <== FR30 f_nontriv=17/36=0.4722 lies in this bin (FR30 E<=8.770)" if lo <= 17 / 36 < hi else ""
        log(f"   f in [{lo:.2f},{hi:.2f}): n={len(rs):5d}  E_per min={Es.min():.4f} 10%={np.percentile(Es,10):.4f} median={np.median(Es):.4f} 90%={np.percentile(Es,90):.4f} max={Es.max():.4f}  k's={sorted(set(r['k'] for r in rs))}{mark}")
    near = [r for r in allr if abs(r['f_nontriv'] - 17 / 36) < 0.03]
    if near:
        Es = np.array([r['E'] for r in near])
        log(f" decorations with |f_nontriv - 17/36| < 0.03: n={len(near)}  E_per min={Es.min():.4f} median={np.median(Es):.4f} max={Es.max():.4f};"
            f"  number with E_per >= 8.770: {int(np.sum(Es >= 8.770))} ({np.mean(Es >= 8.770):.3f});  >= 8.5: {int(np.sum(Es >= 8.5))}")
    near2 = [r for r in allr if abs(r['f_nontriv'] - 17 / 36) < 0.03 and abs(r['f_traceless'] - 55 / 144) < 0.04 and abs(r['f_minus1'] - 13 / 144) < 0.04]
    if near2:
        Es = np.array([r['E'] for r in near2])
        log(f" decorations matching ALL THREE FR30 class fractions within (0.03,0.04,0.04): n={len(near2)}  E_per min={Es.min():.4f} median={np.median(Es):.4f} max={Es.max():.4f}")
        for r in sorted(near2, key=lambda r: -r['E'])[:4]:
            log(f"     {r['label'][:70]:70s} E_per={r['E']:.5f} theta={np.round(r['theta'],3).tolist()} flux nontriv={r['f_nontriv']:.4f} traceless={r['f_traceless']:.4f} -1={r['f_minus1']:.4f}")
    f = np.array([r['f_nontriv'] for r in allr]); E = np.array([r['E'] for r in allr])
    ft = np.array([r['f_traceless'] for r in allr]); fm = np.array([r['f_minus1'] for r in allr])
    log(f" Pearson corr(E_per, f_nontriv) = {np.corrcoef(E, f)[0, 1]:.4f};  corr(E_per, f_traceless) = {np.corrcoef(E, ft)[0, 1]:.4f};  corr(E_per, f_-1) = {np.corrcoef(E, fm)[0, 1]:.4f}")
    A = np.c_[np.ones_like(f), ft, fm]; coef, res, *_ = np.linalg.lstsq(A, E, rcond=None); pred = A @ coef
    log(f" least-squares E_per ~ {coef[0]:.3f} + {coef[1]:.3f} f_traceless + {coef[2]:.3f} f_-1 ;  rms residual {np.sqrt(np.mean((E-pred)**2)):.4f} (sd of E_per {E.std():.4f});"
        f"  prediction at the FR30 fractions: {coef[0] + coef[1]*55/144 + coef[2]*13/144:.4f}  (FR30 actual <= 8.770)")
    log(f" minimum location: Gamma {sum(r['gamma'] for r in allr)}, other TRIM {sum(r['trim'] and not r['gamma'] for r in allr)}, generic {sum(not r['trim'] for r in allr)} of {len(allr)};"
        f"  lowest band exactly degenerate at generic q: {sum(r['gap12_generic'] < 1e-9 for r in allr)}")
    log(f"[stage T done in {time.time()-T0:.0f}s]")

# ----------------------------------------------------------------------------------------------------------------
def stage_B():
    """Supercell sanity checks for the k=8 FR30-frame (natural bijection) decoration."""
    log("=" * 100); log("B. SUPERCELL CHECKS, k=8 L'=2L, FR30 frames (natural bijection)")
    S8 = 2 * np.eye(3, dtype=int); dec0 = Decoration(S8, [np.eye(3, dtype=int)] * 8)
    eps_of = lambda i: tuple(int(x) % 2 for x in dec0.reps[i])
    nat = [0 if eps_of(i) == (1, 1, 1) else 1 + U3.index(eps_of(i)) for i in range(8)]
    dec = Decoration(S8, [FR30_FRAMES[p] for p in nat])
    r = band_minimum(dec, ngrid=12)
    log(f" Bloch band bottom (12^3 grid + Nelder-Mead): E_per = {r['E']:.9f} at theta={np.round(r['theta'],5).tolist()}  gap12={r['gap12']:.2e}")
    hops = dec.hops()
    def supercell(N, torus):
        """N x N x N copies of the L' cell: chairs indexed by (alpha in [0,N)^3, coset).  torus=True identifies
        alpha mod N (periodic); torus=False keeps only panels with both chairs inside (open, pinned diagonal 24)."""
        idx = lambda al, c: ((al[0] * N + al[1]) * N + al[2]) * 8 + c
        n = N ** 3 * 8; rows, cols, vals = [], [], []
        for a in range(n):
            for s in range(2): rows.append(2 * a + s); cols.append(2 * a + s); vals.append(24.0)
        SinvT = np.linalg.inv(S8.T)
        for al in itertools.product(range(N), repeat=3):
            al = np.array(al)
            for (c, c2, d, C) in hops:
                # alpha of the neighbour: L'-coordinates of (rep_c + m_d - rep_c2)
                md = Lcoords(d); dal = SinvT @ (dec.reps[c] + md - dec.reps[c2]); dali = np.rint(dal).astype(int)
                assert np.allclose(dal, dali)
                al2 = al + dali
                if torus: al2 = al2 % N
                elif (al2 < 0).any() or (al2 >= N).any(): continue
                a, b = idx(al, c), idx(al2, c2)
                for s in range(2):
                    for t in range(2): rows.append(2 * a + s); cols.append(2 * b + t); vals.append(-C[s, t])
        H = sps.coo_matrix((vals, (rows, cols)), shape=(2 * n, 2 * n)).tocsr()
        assert abs(H - H.getH()).max() < 1e-12
        return H
    for N in (2, 4):
        H = supercell(N, torus=True); w = np.linalg.eigvalsh(H.toarray())
        th = np.array(list(itertools.product(np.arange(N) / N, repeat=3)))
        Q = (2 * np.pi * np.linalg.solve(dec.Bp.astype(float), th.T)).T
        wb = np.sort(np.linalg.eigvalsh(dec.Hq_batch(Q)).ravel())
        log(f" torus {N}x{N}x{N} supercell (dim {H.shape[0]}): lowest {np.round(w[:4],6).tolist()};  union of Bloch spectra on the commensurate {N}^3 grid: lowest {np.round(wb[:4],6).tolist()};"
            f"  max |sorted spectra difference| = {np.max(np.abs(w - wb)):.2e}")
    for N in (2, 4, 6, 8):
        H = supercell(N, torus=False)
        if H.shape[0] <= 2048: w = np.linalg.eigvalsh(H.toarray())[:4]
        else:
            w = spl.eigsh(H, k=4, sigma=0.0, which='LM', return_eigenvectors=False); w = np.sort(w)
        log(f" open pinned {N}x{N}x{N} supercell (dim {H.shape[0]}, hard walls): lowest {np.round(w[:4],6).tolist()}  excess over E_per: {w[0]-r['E']:.6f}  x N^2 = {(w[0]-r['E'])*N**2:.4f}")
    log(f"[stage B done in {time.time()-T0:.0f}s]")

def stage_C(j):
    """Exhaustive: all 8! bijections of the FR30 level-1 frames onto the cosets of 2L, chunk j of 4 (10080 each)."""
    log("=" * 100); log(f"C{j}. BIJECTIONS OF THE FR30 LEVEL-1 FRAMES ONTO L/2L, chunk {j}/4 (10080 of 40320), coarse minimiser (validated to 1e-13)")
    S8 = 2 * np.eye(3, dtype=int)
    perms = list(itertools.permutations(range(8)))[10080 * j:10080 * (j + 1)]
    Es = []; t0 = time.time()
    for i, perm in enumerate(perms):
        dec = Decoration(S8, [FR30_FRAMES[p] for p in perm])
        Es.append(band_minimum(dec, ngrid=4, nstart=2)['E'])
        if time.time() - t0 > 1000: log(f"   time budget reached after {i+1} bijections"); break
    Es = np.array(Es)
    log(f" bijections evaluated: {len(Es)};  E_per min={Es.min():.6f} max={Es.max():.6f} mean={Es.mean():.5f} sd={Es.std():.5f};  fraction >= 8.770: {np.mean(Es >= 8.770):.4f}")
    hist, edges = np.histogram(Es, bins=np.arange(4.0, 13.01, 0.5))
    log(" histogram (0.5 bins): " + ", ".join(f"[{lo:.1f},{hi:.1f}):{h}" for h, lo, hi in zip(hist, edges[:-1], edges[1:]) if h))
    vals, cnts = np.unique(np.round(Es, 6), return_counts=True)
    log(f" distinct E_per values (6 decimals): {len(vals)}; the five largest: {[(float(v), int(c)) for v, c in zip(vals[-5:], cnts[-5:])]}")
    np.save(REC_FILE.replace('records.jsonl', f'bijections_chunk{j}.npy'), Es)
    for i in np.argsort(Es)[-2:]:
        rec = analyse(Decoration(S8, [FR30_FRAMES[p] for p in perms[i]]), f"k=8 2L FR30 bijection {list(perms[i])} [chunk {j} top]"); print_rec(rec)
    log(f"[stage C{j} done in {time.time()-T0:.0f}s]")

def stage_S():
    """Proposition (quaternionic Bloch symmetry).  For the pure-translation chair crystal with an L'-periodic frame
    field, if 2L is contained in L' then H(q) = H(-q) for all q, H(q) commutes with the antiunitary
    Theta = 1 (x) i sigma_y K (Theta^2 = -1), and every Bloch band is exactly two-fold degenerate at every q.
    Proof: the panel set of a chair is invariant under (d, n) -> (-d, -n) (the same panel seen from the neighbour;
    all chairs are translates).  If 2L is in L', then m_a + m_d and m_a - m_d lie in the same coset (their
    difference 2 m_d is in 2L), so the two panels (d, n) and (-d, -n) join the same pair of cosets (a, b), and their
    links coincide: (sigma.M_a^T(-n))(sigma.M_b^T(-n)) = (sigma.M_a^T n)(sigma.M_b^T n).  Hence
    A(q) = sum over panel pairs of 2 cos(q.d) |a><b| (x) C, a REAL combination of matrices with SU(2) blocks, which is
    quaternionic (commutes with Theta).  []  The converse direction is tested numerically below (when 2L is not in L',
    H(q) differs from H(-q) and the pairs split at generic q)."""
    log("=" * 100); log("S. QUATERNIONIC BLOCH SYMMETRY: numerical check of the proposition (see docstring of stage_S) on random decorations")
    rng = np.random.default_rng(3); I3 = np.eye(3, dtype=int)
    cases = [(np.diag([2, 2, 1]), "k=4 diag(2,2,1)"), (np.diag([2, 1, 2]), "k=4 diag(2,1,2)"), (np.array([[2, 1, 0], [0, 2, 0], [0, 0, 1]]), "k=4 [[2,1,0],[0,2,0],[0,0,1]]"),
             (np.diag([1, 1, 4]), "k=4 diag(1,1,4)"), (np.array([[1, 0, 1], [0, 1, 2], [0, 0, 4]]), "k=4 [[1,0,1],[0,1,2],[0,0,4]]"),
             (2 * I3, "k=8 2I"), (np.diag([1, 2, 4]), "k=8 diag(1,2,4)"), (np.diag([1, 1, 8]), "k=8 diag(1,1,8)")] + [(S, f"k=2 {S.tolist()}") for S in hnf_sublattices(2)]
    for S, lab in cases:
        k = int(round(np.linalg.det(S))); dec = Decoration(S, [I3] + [SO3Z[g] for g in rng.integers(0, 24, k - 1)])
        Theta = np.kron(np.eye(k), 1j * SIG[1])
        contains2L = np.allclose(np.linalg.solve(S.T.astype(float), 2 * np.eye(3)), np.rint(np.linalg.solve(S.T.astype(float), 2 * np.eye(3))))
        r = []
        for q in rng.normal(size=(6, 3)):
            H = dec.Hq(q); w = np.linalg.eigvalsh(H)
            r.append((np.abs(H - dec.Hq(-q)).max(), np.abs(Theta @ H.conj() @ Theta.conj().T - H).max(), np.min(w[1::2] - w[0::2])))
        r = np.array(r)
        log(f" {lab:34s} 2L in L': {str(contains2L):5s}  max|H(q)-H(-q)|={r[:,0].max():.1e}  max|Theta H(q) Theta^-1 - H(q)|={r[:,1].max():.1e}  min pair splitting at random q={r[:,2].min():.2e}")
    log(f"[stage S done in {time.time()-T0:.0f}s]")

if __name__ == "__main__":
    stage = sys.argv[1] if len(sys.argv) > 1 else 'A1'
    if stage == 'A1': stage_A1()
    elif stage == 'A2': stage_A2(int(sys.argv[2]))
    elif stage == 'A3': stage_A3()
    elif stage == 'B': stage_B()
    elif stage == 'C': stage_C(int(sys.argv[2]))
    elif stage == 'T': stage_T()
    elif stage == 'S': stage_S()
