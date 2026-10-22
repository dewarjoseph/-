#!/usr/bin/env python3
"""Phase V-E core: gauge-covariant compressions of the exact Schur boundary operator of FR30/Chair44 supertiles.

OPERATOR (unchanged from Phases V-A..V-D; audit/phase5a_controls.build_H).  H = 24 I - A on l^2(tiles) x C^2,
(A psi)_a = sum over shared unit panels f = (a, b) of C_ab psi_b, C_ab = (sigma.M_a^T n_f)(sigma.M_b^T n_f) in Q8, C_ba = C_ab^+.
Every 2x2 block of H is a real multiple of a unit quaternion, so H commutes with T = (1 x i sigma_y) K, T^2 = -1 (Kramers).
A level-L parent has depth-1 children c = 0..7 (tile index // 8^(L-1)); S_c = tiles of c with a panel neighbour outside c
(another child or missing), I_c = the rest (Phase V-D partition, audit/phase5d_schur.partition).

POLE (SPECTRAL) REPRESENTATION OF THE CHILD RESPONSE.  With H_{I_c I_c} = Q_c diag(l_cj) Q_c^+ and B_c = Q_c^+ H_{I_c S_c},
    R_c(E) = H_{S_c S_c} - E - B_c^+ diag(1/(l_cj - E)) B_c          (exact for E not in spec H_{I_c I_c}),
    K(E)   = (+)_c R_c(E) + Off,   Off = inter-child block of H_SS (= -V_SS of V-D).
For a subspace W = (+)_c W_c with orthonormal basis P = (+)_c P_c (every basis below is CHILD-LOCAL):
    M_W(E) = P^+ K(E) P = (+)_c [A_c - E - C_c^+ diag(1/(l_c - E)) C_c] + P^+ Off P,   A_c = P_c^+ H_SS,c P_c,  C_c = B_c P_c
    M_W'(E) = -(+)_c [I + C_c^+ diag(1/(l_c - E)^2) C_c] <= -I,   M_W''(E) = -2 (+)_c C_c^+ diag(1/(l_c - E)^3) C_c <= 0 (E < l_min).
Hence g_W(E) = lambda_min M_W(E) is strictly decreasing (slope <= -1) and CONCAVE on E < lambda_II = min_c l_c0; its root E_W
(if it lies below lambda_II) is found by Newton's method from the right, which converges monotonically (concavity).  E_W >= E_0
= lambda_min(H), with E_W - E_0 <= g_W(E_0) (Theorem E3 of the report); W = S gives E_W = E_0 exactly (Theorem D1 of V-D).

GEOMETRY OF THE INTERFACE.  For a surface tile a of child c, F(a) = set of OTHER children owning a panel neighbour of a.
    outer tile: F(a) empty (only missing neighbours: the parent's own pinned boundary)
    face tile : |F(a)| = 1        hinge (edge) tile: |F(a)| = 2        corner tile: |F(a)| >= 3
Face (c, c') = face tiles of c with F = {c'};  hinge (c, {c', c''});  corners of c.  The contact graph of the 8 children is the
same at every level (self-similar geometry), so the number of faces does not depend on L.

BASIS FAMILIES (all child-local, all Kramers-complete, all gauge-covariant; frozen in deliverables/PHASE5E_PROTOCOL.md):
    child(k)     k lowest Kramers pairs of R_c(E_REF) per child (V-D's reduced model)
    face(k)      k lowest pairs of R_c(E_REF)[F, F] on every face F (interface-localized, H1)
    fec(k)       face(k) + k lowest pairs on every hinge + all corner tiles (face/edge/corner hierarchy, H2)
    patch(d, k)  k lowest pairs of R_c(E_REF)[P, P] on every patch P = (interface tiles of c) n (depth-d subtree) (hierarchy/wavelet-like)
    tiles(mask)  coordinate subspace of a tile set (used for 'interface' = all interface tiles, and for the ADAPTIVE basis whose
                 tile set is chosen from training-rule ground states only)
    exact        all of S (reference ceiling; not a compression)
A multiplet is never split: after the 2k-th eigenvalue, further eigenvalues within DEG_TOL are added (gauge covariance needs
whole eigenspaces of covariant operators; see Lemma E2 of the report).
"""
import os, sys, types, time, json
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); RES = os.path.join(HERE, 'results')
try:
    import resource  # noqa: F401
except ImportError:                                     # Windows: the V-B/V-D modules import `resource` only for RSS logging
    sys.modules['resource'] = types.SimpleNamespace(getrusage=lambda *a: types.SimpleNamespace(ru_maxrss=0), RUSAGE_SELF=0)
import numpy as np, scipy.linalg as sla, scipy.sparse as sps, scipy.sparse.linalg as spl
import phase5d_schur as d
from independent_clifford_q8_audit import FR30

E_REF = 7.0; DEG_TOL = 1e-8; NEWTON_TOL = 1e-12
spinor = d.spinor

def random_gauge(n, seed):
    rng = np.random.default_rng(seed); Us = []
    for _ in range(n):
        q = rng.normal(size=4); q /= np.linalg.norm(q)
        Us.append(np.array([[q[0] + 1j * q[3], q[2] + 1j * q[1]], [-q[2] + 1j * q[1], q[0] - 1j * q[3]]]))
    return sps.block_diag(Us, format='csr')

def kramers_partner(v):
    """T v with T = (1 x i sigma_y) K: per tile (a, b) -> (conj b, -conj a)."""
    w = np.empty_like(v); w[0::2] = np.conj(v[1::2]); w[1::2] = -np.conj(v[0::2]); return w

def low_modes(M, k):
    """k lowest Kramers pairs of the Hermitian matrix M, multiplets completed (never split a degenerate eigenspace)."""
    w, U = np.linalg.eigh(M); m = min(2 * k, len(w))
    while m < len(w) and w[m] - w[m - 1] < DEG_TOL: m += 1
    return U[:, :m], w[:m]

class System:
    """A level-L parent split into its 8 depth-1 children, with the pole representation of every child response."""
    def __init__(self, spec, level, gauge_seed=None, tiles=None):
        t0 = time.time(); self.spec = spec; self.level = level
        self.tiles = d.tiles_of(spec, level) if tiles is None else tiles
        H, edges = d.build(self.tiles); n = len(self.tiles); self.n = n
        if gauge_seed is not None: Gm = random_gauge(n, gauge_seed); H = (Gm @ H @ Gm.conj().T).tocsr()
        self.H = H; self.edges = edges
        self.child, self.surf = d.partition(n, edges, level)
        a = np.array([e[0] for e in edges]); b = np.array([e[1] for e in edges])
        self.deg = np.bincount(a, minlength=n) + np.bincount(b, minlength=n)
        cross = self.child[a] != self.child[b]; F = [set() for _ in range(n)]
        for x, y in zip(a[cross], b[cross]): F[x].add(int(self.child[y])); F[y].add(int(self.child[x]))
        self.F = F
        self.S = [np.nonzero((self.child == c) & self.surf)[0] for c in range(8)]
        self.I = [np.nonzero((self.child == c) & ~self.surf)[0] for c in range(8)]
        self.Sall = np.concatenate(self.S); self.sS = spinor(self.Sall)
        self.offs = np.cumsum([0] + [2 * len(s) for s in self.S])
        Hss = H[self.sS][:, self.sS].tocsr()
        blk = np.repeat(np.arange(8), [2 * len(s) for s in self.S]); coo = Hss.tocoo(); keep = blk[coo.row] != blk[coo.col]
        self.Off = sps.csr_matrix((coo.data[keep], (coo.row[keep], coo.col[keep])), shape=Hss.shape)
        self.HSS, self.B, self.lam = [], [], []
        for c in range(8):
            ss, ii = spinor(self.S[c]), spinor(self.I[c])
            self.HSS.append(H[ss][:, ss].toarray())
            if len(ii):
                HII = H[ii][:, ii].toarray(); l, Q = np.linalg.eigh(HII)
                self.B.append(Q.conj().T @ H[ii][:, ss].toarray()); self.lam.append(l)
            else: self.B.append(np.zeros((0, len(ss)), complex)); self.lam.append(np.zeros(0))
        self.lam_II = min([float(l[0]) for l in self.lam if len(l)] or [np.inf])
        self._Rref = None; self.build_seconds = time.time() - t0

    # ---------------------------------------------------------------- child responses
    def R(self, c, E):
        return self.HSS[c] - E * np.eye(self.HSS[c].shape[0]) - (self.B[c].conj().T * (1.0 / (self.lam[c] - E))) @ self.B[c]
    def Rref(self, c):
        if self._Rref is None: self._Rref = [self.R(cc, E_REF) for cc in range(8)]
        return self._Rref[c]
    def K(self, E): return sla.block_diag(*[self.R(c, E) for c in range(8)]) + self.Off.toarray()
    def Kref(self):
        if getattr(self, '_Kref', None) is None: self._Kref = sla.block_diag(*[self.Rref(c) for c in range(8)]) + self.Off.toarray()
        return self._Kref

    # ---------------------------------------------------------------- interface geometry
    def tile_class(self, c):
        """per surface tile of child c (in S_c order): 'outer' | 'face' | 'hinge' | 'corner', and its foreign set."""
        out = []
        for t in self.S[c]:
            f = self.F[t]; out.append(('outer' if not f else 'face' if len(f) == 1 else 'hinge' if len(f) == 2 else 'corner', frozenset(f)))
        return out
    def groups(self, c, kind):
        """dict label -> positions (indices into S_c) of the tile groups of child c: kind in face | hinge | corner | interface."""
        cl = self.tile_class(c); g = {}
        for p, (k, f) in enumerate(cl):
            if kind == 'interface' and k != 'outer': g.setdefault('interface', []).append(p)
            elif k == kind: g.setdefault(('corner',) if kind == 'corner' else tuple(sorted(f)), []).append(p)
        return {kk: np.array(v) for kk, v in g.items()}
    def patches(self, c, depth):
        cl = self.tile_class(c); anc = self.S[c] // 8 ** (self.level - depth); g = {}
        for p, (k, _) in enumerate(cl):
            if k != 'outer': g.setdefault(int(anc[p]), []).append(p)
        return {kk: np.array(v) for kk, v in g.items()}

class Reduced:
    """Galerkin compression of K(E) onto W = range(P), P = [P_0; ...; P_7] (rows split by child surface blocks, orthonormal
    columns).  Child-local bases have block-diagonal P; two-sided interface bases have columns on two children."""
    def __init__(self, sysm, Ps, name=''):
        self.sys, self.name = sysm, name
        if isinstance(Ps, list):                                   # child-local: list of 8 blocks -> block-diagonal global P
            D = sum(P.shape[1] for P in Ps); Pg = np.zeros((sysm.offs[-1], D), complex); o = 0
            for c, P in enumerate(Ps): Pg[sysm.offs[c]:sysm.offs[c + 1], o:o + P.shape[1]] = P; o += P.shape[1]
        else: Pg = Ps
        self.D = int(Pg.shape[1]); self.Pg = sps.csr_matrix(Pg)
        self.Pc = [Pg[sysm.offs[c]:sysm.offs[c + 1]] for c in range(8)]
        self.act = [c for c in range(8) if np.abs(self.Pc[c]).max(initial=0) > 0]
        self.A = {c: self.Pc[c].conj().T @ sysm.HSS[c] @ self.Pc[c] for c in self.act}
        self.G = {c: self.Pc[c].conj().T @ self.Pc[c] for c in self.act}
        self.C = {c: sysm.B[c] @ self.Pc[c] for c in self.act}
        self.O = (self.Pg.conj().T @ (sysm.Off @ self.Pg)).toarray() if self.D else np.zeros((0, 0))
        self.nev = 0
    def M(self, E):
        M = self.O.copy()
        for c in self.act: M += self.A[c] - E * self.G[c] - (self.C[c].conj().T * (1.0 / (self.sys.lam[c] - E))) @ self.C[c]
        return M
    def dM_quad(self, E, x):
        """x^+ M'(E) x (Hellmann-Feynman derivative of the eigenvalue branch); M' = -I - sum_c C_c^+ diag(1/(l_c - E)^2) C_c."""
        s = -np.vdot(x, x).real
        for c in self.act: y = self.C[c] @ x; s -= float(np.sum(np.abs(y) ** 2 / (self.sys.lam[c] - E) ** 2))
        return s
    def g(self, E, vec=False):
        self.nev += 1; M = self.M(E)
        if M.shape[0] > 1500: w, V = sla.eigh(M, subset_by_index=(0, 1), driver='evr')
        else: w, V = np.linalg.eigh(M)
        return (float(w[0]), V[:, 0]) if vec else float(w[0])
    def root(self, E_start=E_REF, tol=NEWTON_TOL, maxit=60):
        """root of g_W on (-inf, lambda_II); np.nan if g_W > 0 on the whole admissible window.
        g_W is decreasing and concave there, so for a bracket lo < root < hi: the Newton step from lo lands in [root, hi)
        and the chord root lands in (lo, root]; both ends move every iteration (two evaluations per iteration)."""
        hi_max = min(self.sys.lam_II - 1e-9, 48.0); E = min(E_start, hi_max - 1e-6); gE, x = self.g(E, True); it = 0
        hi, ghi = np.inf, None
        while gE <= 0:
            hi, ghi = E, gE; E = E - 1.0; gE, x = self.g(E, True); it += 1
            if it > maxit: raise RuntimeError('no left bracket')
        lo, glo, xlo = E, gE, x
        if not np.isfinite(hi):
            En = lo - glo / self.dM_quad(lo, xlo)
            if En < hi_max: hi, ghi = En, self.g(En)
            if not np.isfinite(hi) or ghi > 0:
                ghm = self.g(hi_max)
                if ghm > 0: return np.nan, it
                hi, ghi = hi_max, ghm
        for _ in range(maxit):
            it += 1
            if hi - lo < tol: break
            En = lo - glo / self.dM_quad(lo, xlo)                    # Newton from the left: in [root, hi) by concavity
            if not (lo < En < hi): En = 0.5 * (lo + hi)              # overshoot past the bracket (pole side): bisect
            gn, xn = self.g(En, True)
            if gn > 0: lo, glo, xlo = En, gn, xn
            else: hi, ghi = En, gn
            if hi - lo < tol: break
            Ec = lo - glo * (hi - lo) / (ghi - glo)                  # chord: in (lo, root] by concavity
            if not (lo + 0.02 * (hi - lo) < Ec < hi): continue       # useless next to a pole: skip
            gc, xc = self.g(Ec, True)
            if gc > 0: lo, glo, xlo = Ec, gc, xc
            else: hi, ghi = Ec, gc
        return float(0.5 * (lo + hi)), it

# ------------------------------------------------------------------ bases
def P_child(s, k):  return [low_modes(s.Rref(c), k)[0] for c in range(8)]
def _group_modes(s, c, groups, k, full=()):
    R = s.Rref(c); m = 2 * len(s.S[c]); cols = []
    for lab, pos in groups.items():
        sp = spinor(pos)
        if lab in full or k is None: U = np.eye(len(sp), dtype=complex)
        else: U, _ = low_modes(R[np.ix_(sp, sp)], k)
        blk = np.zeros((m, U.shape[1]), complex); blk[sp] = U; cols.append(blk)
    return np.hstack(cols) if cols else np.zeros((m, 0), complex)
def P_face(s, k):   return [_group_modes(s, c, s.groups(c, 'face'), k) for c in range(8)]
def P_fec(s, k):
    out = []
    for c in range(8):
        g = s.groups(c, 'face'); g.update(s.groups(c, 'hinge')); g.update(s.groups(c, 'corner'))
        out.append(_group_modes(s, c, g, k, full=(('corner',),)))
    return out
def P_patch(s, depth, k): return [_group_modes(s, c, s.patches(c, depth), k) for c in range(8)]
def P_tiles(s, mask):
    """coordinate subspace of the surface tiles with mask[tile] True (mask over all n tiles)."""
    out = []
    for c in range(8):
        pos = np.nonzero(mask[s.S[c]])[0]; sp = spinor(pos); P = np.zeros((2 * len(s.S[c]), len(sp)), complex)
        P[sp, np.arange(len(sp))] = 1.0; out.append(P)
    return out
def P_iface2(s, k):
    """two-sided interface modes: for every adjacent child pair {c, c'}, the k lowest Kramers pairs of the GLUED operator
    K(E_REF) restricted to the face tiles of c facing c' and of c' facing c (bonding modes of the seam; columns span two
    children).  Faces of different pairs are disjoint, so the columns are orthonormal."""
    Kref = s.Kref(); pairs = {}
    for c in range(8):
        for lab, pos in s.groups(c, 'face').items():
            pairs.setdefault(frozenset((c, lab[0])), []).append((c, pos))
    cols = []
    for pr, parts in sorted(pairs.items(), key=lambda t: sorted(t[0])):
        idx = np.concatenate([s.offs[c] + spinor(pos) for c, pos in parts])
        U, _ = low_modes(Kref[np.ix_(idx, idx)], k); blk = np.zeros((s.offs[-1], U.shape[1]), complex); blk[idx] = U; cols.append(blk)
    return np.hstack(cols)
def interface_mask(s):
    m = np.zeros(s.n, bool)
    for t in s.Sall:
        if s.F[t]: m[t] = True
    return m
def P_exact(s): return [np.eye(2 * len(s.S[c]), dtype=complex) for c in range(8)]

FAMILIES = {   # frozen grids (deliverables/PHASE5E_PROTOCOL.md)
    'child': [1, 2, 4, 8, 16, 32, 64],
    'face': [1, 2, 4, 8, 16],
    'fec': [1, 2, 4, 8, 16],
    'patch2': [1, 2, 4, 8],
    'patch3': [1, 2],
    'iface2': [1, 2, 4, 8, 16, 32],
}
def make_basis(s, fam, k):
    if fam == 'child': return P_child(s, k)
    if fam == 'face': return P_face(s, k)
    if fam == 'fec': return P_fec(s, k)
    if fam == 'patch2': return P_patch(s, 2, k)
    if fam == 'patch3': return P_patch(s, 3, k)
    if fam == 'iface2': return P_iface2(s, k)
    if fam == 'interface': return P_tiles(s, interface_mask(s))
    if fam == 'exact': return P_exact(s)
    raise ValueError(fam)

# ------------------------------------------------------------------ geometry keys (for the adaptive basis and SVD analyses)
def geo_key(tile): return min(tile[2])                       # lowest cube of the chair: a rule-independent label of the tile
def geo_keys(s): return [geo_key(t) for t in s.tiles]

def ground_state(s, E0=None, k=2):
    """exact lowest Kramers pair of H (shift-invert near E0 if given, else dense for small n)."""
    if s.n <= 600:
        w, V = np.linalg.eigh(s.H.toarray()); return w[:k], kramers_pair(V[:, 0])
    sig = (E0 - 1e-3) if E0 is not None else -1e-3          # H >= 0, so shift-invert at 0 returns the lowest eigenvalues
    w, V = spl.eigsh(s.H.tocsc(), k=k, sigma=sig, which='LM', tol=1e-12)
    o = np.argsort(w); return w[o], kramers_pair(V[:, o[0]])

def kramers_pair(psi):
    """orthonormal Kramers pair {psi, T psi} from one ground vector (ARPACK may return only one copy of a doublet)."""
    v = psi / np.linalg.norm(psi); w = kramers_partner(v); w -= v * np.vdot(v, w); w /= np.linalg.norm(w)
    return np.c_[v, w]

def captured(s, red, psi):
    """fraction of the exact ground pair's S-weight retained by W, and of total weight on S (psi: n x 2 Kramers pair)."""
    PS = psi[s.sS]; tot = float(np.sum(np.abs(PS) ** 2)); pr = red.Pg.conj().T @ PS
    return float(np.sum(np.abs(pr) ** 2) / tot), tot / float(np.sum(np.abs(psi) ** 2))
