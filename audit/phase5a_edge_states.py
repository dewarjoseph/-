"""
Phase 5a / Task B1 (H2, H3): reproduce the spectral bottoms of the Clifford-Q8 hopping operator on FR30 Chair44
patches and determine the nature (extended / localized / critical) of the lowest eigenstates, with built-in controls.

OPERATOR DEFINITION (exact; everything below is what the code builds)
  Graph G_L : vertices = the n = 8^L chair tiles of the level-L FR30 supertile patch, tiles_at_level(FR30, L) from
      audit/independent_clifford_q8_audit.py, in depth-first generation order (tile index a = sum_j c_j 8^(L-1-j),
      c_0 = child index at the top level).  Tile a carries a frame M_a in SO(3,Z) and 7 unit cubes.
      Edges = shared unit panels: one edge f=(a,b) per unit square face shared by a cube of tile a and a cube of a
      different tile b (panel_edges; a multigraph: adjacent tiles share 3 or 4 panels and get one edge per panel).
      Each edge carries the ambient unit normal n_f (the +x, +y or +z axis along which the two cubes are adjacent);
      the link does not depend on the sign of n_f.  deg(a) = number of shared panels of tile a (= 24 for every tile
      of the infinite tiling; < 24 exactly for the tiles on the boundary of the finite patch, called boundary tiles).
  Hilbert space : l^2(tiles) (x) C^2, complex dimension 2n, standard inner product; psi[2a+s], s = 0, 1.
  Links : C_ab = (sigma . M_a^T n_f)(sigma . M_b^T n_f), an element of Q8 = {+-I, +-i sigma_x, +-i sigma_y, +-i sigma_z}
      (unitary, unit magnitude), C_ba = C_ab^dagger.
  Adjacency : (A psi)_a = sum_{panels f=(a,b)} C_ab psi_b   (Hermitian 2n x 2n).
  H_free = D - A,  D = diag(deg(a)) (x) I_2 : open boundary; positive semidefinite (sum over panels of the
      2-site terms [[I,-C],[-C^+,I]] >= 0).
  H_pin  = 24 I - A = H_free + diag(24 - deg(a)) (x) I_2 : missing neighbours act as hard walls; H_pin is the compression
      of the bulk operator 24 - A_infty to the patch, so lambda_min(H_pin, L) >= inf spec(24 - A_infty) and the
      sequence is non-increasing along nested patches.
  Trivial control : the same graph with all C_ab = I_2, i.e. H = (24 - A_0) (x) I_2, A_0 = panel-count adjacency
      (spin-degenerate; computed on the n x n real tile operator).
  Sign / normalization : hopping amplitude 1 (minus sign in front of A), so spec(H) is contained in [0, 48].
  Residual : r = ||H psi - lambda psi||_2 for ||psi||_2 = 1, computed with the exact sparse operator for every
      reported eigenpair.
TILE IPR (used throughout) : for a normalized eigenvector psi, p_a = |psi[2a]|^2 + |psi[2a+1]|^2 (sum_a p_a = 1);
      IPR = sum_a p_a^2; participation number P = 1/IPR; a state uniform over all n tiles has IPR = 1/n, a state
      uniform over s tiles has IPR = 1/s.  Generalised IPR_q = sum_a p_a^q (q = 2 is the IPR).
      Note: p_a is identical for every vector of a Kramers doublet {psi, (i sigma_y K) psi}, so the tile IPR is well
      defined on each doublet; it is NOT basis independent across accidental near-degeneracies between doublets.
INTERFACE DEPTH PROFILE : for d = 1..L a tile a is a depth-d interface tile iff it shares a panel with a tile b with
      a // 8^(L-d) != b // 8^(L-d) (a and b lie in different level-(L-d) children).  Reported: the weight sum_{a in I_d} p_a
      versus the fraction |I_d| / n (d = 1 reproduces the counts T_L = 8, 53, 269, 1277, 5597 of phase 3).
BOX COUNTING : S_q(d) = sum over the 8^d level-(L-d) children c of (sum_{a in c} p_a)^q for d = 0..L
      (S_q(0) = 1, S_q(L) = IPR_q).  Uniform extended state: S_2(d) = 8^(-d); state inside one child: S_2(d) = 1.

SOLVERS : dense scipy.linalg.eigh (subset of the lowest eigenpairs) for dimension <= 8192; for larger dimension a
      Chebyshev-filtered subspace iteration (Zhou-Saad scaled filter, block matvecs with the exact sparse CSR
      operator, Rayleigh-Ritz, block m >= K, exact residuals every pass) followed by a matrix-free LOBPCG cross-check of the lowest 6 eigenvalues
      with the diagonal preconditioner of audit/phase5_bulk_bottom_lobpcg.py (seed 0).  All random seeds fixed.
Run from the repository root (<= 3.5 GB, <= 40 min per level):
      python3 -u -I audit/phase5a_edge_states.py --level 4 --K 128
Outputs: audit/results/phase5a_edge_states_level{L}.json and audit/results/phase5a_edge_states_level{L}.txt
"""
import os, sys, time, json, argparse, collections, resource
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import numpy as np, scipy.sparse as sps, scipy.sparse.linalg as spl, scipy.linalg as sla
from independent_clifford_q8_audit import FR30, U3, perm_mat, tiles_at_level, panel_edges, clifford_link, q8label, SIG

Q8_NAMES = ['+1', '-1', '+i', '-i', '+j', '-j', '+k', '-k']
Q8_MATS = {'+1': np.eye(2, dtype=complex), '-1': -np.eye(2, dtype=complex)}
for k, nm in enumerate('ijk'):
    Q8_MATS['+' + nm] = 1j * SIG[k]; Q8_MATS['-' + nm] = -1j * SIG[k]

def log(msg, fh=None):
    print(msg, flush=True)
    if fh is not None: fh.write(msg + "\n"); fh.flush()

def maxrss_gb():
    return resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 1e6

# ----------------------------------------------------------------------------------------------------------------
# Graph and links
# ----------------------------------------------------------------------------------------------------------------
class Patch:
    """Level-L FR30 patch: tiles, panel edges, Q8 link label of every edge, degrees, interface masks.
    method='objects': the primitives tiles_at_level / panel_edges / clifford_link of independent_clifford_q8_audit.py.
    method='grid'   : a vectorized re-implementation (dense owner grid of unit cubes) with the same depth-first tile
                      order; used for level 6 (memory) and cross-validated against 'objects' at levels 2-5."""
    def __init__(self, level, method='objects'):
        t0 = time.time()
        self.level = level; self.method = method
        if method == 'objects':
            tiles = tiles_at_level(FR30, level)
            owner, edges = panel_edges(tiles)
            self.n = n = len(tiles); E = len(edges)
            self.ea = np.fromiter((e[0] for e in edges), dtype=np.int64, count=E)
            self.eb = np.fromiter((e[1] for e in edges), dtype=np.int64, count=E)
            self.eax = np.fromiter((int(np.argmax(e[2])) for e in edges), dtype=np.int64, count=E)
            Gall = np.array([G for G, _, _ in tiles], dtype=np.int64)
            del tiles, owner, edges
        else:
            Gall, Tall = self._poses(level)
            self.n = n = Gall.shape[0]
            base = np.array([[2*u[0]+1, 2*u[1]+1, 2*u[2]+1] for u in U3], dtype=np.int64)           # 7 cube centres (doubled)
            cubes = (np.einsum('pij,cj->pci', Gall, base) + 2*Tall[:, None, :] - 1) // 2            # (n,7,3) cube corners
            S = 2 ** (level + 1)
            assert cubes.min() >= 0 and cubes.max() < S
            owner = np.full((S, S, S), -1, dtype=np.int64)
            flat = cubes.reshape(-1, 3)
            owner[flat[:, 0], flat[:, 1], flat[:, 2]] = np.repeat(np.arange(n), 7)
            assert (owner >= 0).sum() == 7 * n, "overlapping cubes"
            ea, eb, eax = [], [], []
            for ax in range(3):
                o1 = np.moveaxis(owner, ax, 0)[:-1]; o2 = np.moveaxis(owner, ax, 0)[1:]
                sel = (o1 >= 0) & (o2 >= 0) & (o1 != o2)
                ea.append(o1[sel]); eb.append(o2[sel]); eax.append(np.full(int(sel.sum()), ax, dtype=np.int64))
            self.ea = np.concatenate(ea); self.eb = np.concatenate(eb); self.eax = np.concatenate(eax); E = len(self.ea)
            del owner, cubes, flat
        # frames (24 distinct elements of SO(3,Z)) and the link label of every edge via a (frame_a, frame_b, axis) table
        keys, fid = np.unique(Gall.reshape(n, 9), axis=0, return_inverse=True)
        fid = fid.reshape(-1).astype(np.int64)
        framelist = [k.reshape(3, 3) for k in keys]
        self.frames = framelist; F = len(framelist)
        table = np.empty((F, F, 3), dtype=np.int64)
        for i in range(F):
            for j in range(F):
                for ax in range(3):
                    nf = np.zeros(3, dtype=np.int64); nf[ax] = 1
                    name = q8label(clifford_link(framelist[i], framelist[j], nf))
                    assert name != 'other', "link not in Q8"
                    table[i, j, ax] = Q8_NAMES.index(name)
        self.fid = fid
        self.lab = table[fid[self.ea], fid[self.eb], self.eax]
        self.deg = np.bincount(self.ea, minlength=n) + np.bincount(self.eb, minlength=n)
        assert self.deg.max() == 24
        self.boundary = self.deg < 24
        # depth-d interface masks, d = 1..L
        self.interface = {}
        for d in range(1, level + 1):
            q = 8 ** (level - d)
            cross = (self.ea // q) != (self.eb // q)
            m = np.zeros(n, dtype=bool)
            m[self.ea[cross]] = True; m[self.eb[cross]] = True
            self.interface[d] = m
        self.build_time = time.time() - t0
        self.label_counts = dict(collections.Counter(Q8_NAMES[i] for i in self.lab.tolist()))

    @staticmethod
    def _poses(level):
        """Vectorized copy of the pose recursion of tiles_at_level (same depth-first order)."""
        opG = np.array([perm_mat(FR30['0'])] + [np.diag([1-2*v[0], 1-2*v[1], 1-2*v[2]]) @ perm_mat(FR30[v]) for v in U3], dtype=np.int64)
        opT = np.array([[1, 1, 1]] + [[4*v[0], 4*v[1], 4*v[2]] for v in U3], dtype=np.int64)
        Gs = np.eye(3, dtype=np.int64)[None]; Ts = np.zeros((1, 3), dtype=np.int64)
        for _ in range(level):
            Gn = np.einsum('pij,ojk->poik', Gs, opG).reshape(-1, 3, 3)
            Tn = (2 * Ts[:, None, :] + np.einsum('pij,oj->poi', Gs, opT)).reshape(-1, 3)
            Gs, Ts = Gn, Tn
        return Gs, Ts

    def canonical_edge_multiset(self):
        """Sorted array of (min(a,b), max(a,b), label of C_{min,max}) for cross-validation of the two builders."""
        a, b, l = self.ea.copy(), self.eb.copy(), self.lab.copy()
        sw = a > b
        a[sw], b[sw] = self.eb[sw], self.ea[sw]
        l[sw] = np.where(l[sw] >= 2, l[sw] ^ 1, l[sw])          # dagger: +-1 fixed, +-i sigma_k -> -+ i sigma_k
        arr = np.stack([a, b, l], axis=1)
        return arr[np.lexsort((arr[:, 2], arr[:, 1], arr[:, 0]))]

    # ---- exact sparse operators -------------------------------------------------------------------------------
    def sparse_H(self, pinned, trivial=False):
        """Exact 2n x 2n complex CSR matrix of H_pin (pinned=True) or H_free, Clifford links (trivial=False) or identity links."""
        n, E = self.n, len(self.ea)
        d = np.full(n, 24.0) if pinned else self.deg.astype(float)
        rows = [np.arange(2 * n)]; cols = [np.arange(2 * n)]; vals = [np.repeat(d, 2).astype(complex)]
        for li, name in enumerate(Q8_NAMES):
            sel = np.nonzero(self.lab == li)[0] if not trivial else (np.arange(E) if li == 0 else np.array([], dtype=np.int64))
            if len(sel) == 0: continue
            C = Q8_MATS[name]; a = self.ea[sel]; b = self.eb[sel]
            for r in range(2):
                for c in range(2):
                    if C[r, c] != 0:
                        rows.append(2 * a + r); cols.append(2 * b + c); vals.append(np.full(len(sel), -C[r, c]))
                        rows.append(2 * b + c); cols.append(2 * a + r); vals.append(np.full(len(sel), -np.conj(C[r, c])))
        H = sps.csr_matrix((np.concatenate(vals), (np.concatenate(rows), np.concatenate(cols))), shape=(2 * n, 2 * n))
        H.sum_duplicates()
        return H

    def sparse_tile_H(self, pinned):
        """Trivial connection: n x n real CSR of 24 - A_0 (pinned) or deg - A_0 (free); H_trivial = this (x) I_2."""
        n = self.n
        d = np.full(n, 24.0) if pinned else self.deg.astype(float)
        rows = np.concatenate([np.arange(n), self.ea, self.eb]); cols = np.concatenate([np.arange(n), self.eb, self.ea])
        vals = np.concatenate([d, -np.ones(len(self.ea)), -np.ones(len(self.ea))])
        H = sps.csr_matrix((vals, (rows, cols)), shape=(n, n)); H.sum_duplicates(); return H

    def reference_H(self, pinned, max_edges=2_000_000):
        """Direct per-edge construction of H (loop over panels, 2x2 blocks), as in audit/phase5_dynamics_boundary.py;
        used only to cross-check sparse_H.  Returns None above max_edges."""
        if len(self.ea) > max_edges: return None
        n = self.n
        rows, cols, vals = [], [], []
        d = np.full(n, 24.0) if pinned else self.deg.astype(float)
        for a in range(n):
            for r in range(2): rows.append(2*a+r); cols.append(2*a+r); vals.append(d[a])
        for a, b, li in zip(self.ea.tolist(), self.eb.tolist(), self.lab.tolist()):
            C = Q8_MATS[Q8_NAMES[li]]
            for r in range(2):
                for c in range(2):
                    rows += [2*a+r, 2*b+c]; cols += [2*b+c, 2*a+r]; vals += [-C[r, c], -np.conj(C[r, c])]
        return sps.coo_matrix((vals, (rows, cols)), shape=(2*n, 2*n)).tocsr()

# ----------------------------------------------------------------------------------------------------------------
# Eigen-solvers
# ----------------------------------------------------------------------------------------------------------------
def dense_lowest(H, K):
    """Lowest K eigenpairs of a sparse Hermitian matrix by dense LAPACK (subset driver)."""
    Hd = H.toarray()
    w, V = sla.eigh(Hd, subset_by_index=(0, K - 1), driver='evr', overwrite_a=True, check_finite=False)
    del Hd
    return w, V

def chebfsi(matvec, N, K, m, lam_max, tol=1e-7, max_passes=200, time_budget=1800.0, deg0=20, deg_max=80,
            seed=0, dtype=complex, logf=None, X0=None):
    """Chebyshev-filtered subspace iteration for the lowest K eigenpairs (block size m >= K), memory-conscious.
    Zhou-Saad scaled filter on [a, lam_max], a = current largest Ritz value of the block; Rayleigh-Ritz on the
    exact operator; stops when the lowest K residuals are below tol (or passes/time exhausted).  Returns Ritz values,
    vectors, exact residual norms (all m), number of block matvecs and the pass history."""
    rng = np.random.default_rng(seed)
    if X0 is None:
        X = rng.standard_normal((N, m))
        if dtype == complex: X = X + 1j * rng.standard_normal((N, m))
        X = X.astype(dtype)
    else:
        X = X0.astype(dtype)
    t0 = time.time(); nmv = 0
    def residuals(X, HX, th, chunk=16):
        r = np.empty(len(th))
        for j in range(0, len(th), chunk):
            r[j:j+chunk] = np.linalg.norm(HX[:, j:j+chunk] - X[:, j:j+chunk] * th[None, j:j+chunk], axis=0)
        return r
    def orthonormalize(Y):
        """In-place CholQR2 (two Cholesky-QR passes; cond(Y) up to ~1e7 gives machine-precision orthogonality);
        falls back to Householder QR if the Gram matrix is numerically singular.  Returns Q (same buffer) and the
        orthogonality error ||Q^H Q - I||_max."""
        for _ in range(2):
            G = Y.conj().T @ Y
            try:
                ev = np.linalg.eigvalsh(G)
                if ev[0] <= 1e-13 * ev[-1]: raise np.linalg.LinAlgError
                Rf = np.linalg.cholesky(G).conj().T          # G = R^H R
                Rinv = sla.solve_triangular(Rf, np.eye(Rf.shape[0], dtype=Rf.dtype), check_finite=False)
                for j in range(0, Y.shape[0], 65536): Y[j:j+65536] = Y[j:j+65536] @ Rinv
            except np.linalg.LinAlgError:
                Q, _ = sla.qr(Y, mode='economic', overwrite_a=True, check_finite=False); Y = Q
        G = Y.conj().T @ Y
        return Y, float(abs(G - np.eye(G.shape[0])).max())
    def rotate_inplace(B, U):
        for j in range(0, B.shape[0], 65536): B[j:j+65536] = B[j:j+65536] @ U
        return B
    # Rayleigh-Ritz, in place on the block Y (which is consumed)
    def rr(Y):
        Q, orth = orthonormalize(Y); del Y
        HQ = matvec(Q)
        G = Q.conj().T @ HQ; G = 0.5 * (G + G.conj().T)
        th, U = np.linalg.eigh(G)
        X = rotate_inplace(Q, U); del Q
        HX = rotate_inplace(HQ, U); del HQ
        return X, HX, th, residuals(X, HX, th), orth
    X, HX, th, res, orth = rr(X); nmv += 1
    del HX
    lam_min_est = th[0]
    deg = deg0
    history = []
    for p in range(max_passes):
        a = float(th[-1]); b = lam_max
        e = (b - a) / 2.0; c = (b + a) / 2.0
        a0 = lam_min_est - 0.05 * (a - lam_min_est) - 1e-3
        sigma = e / (a0 - c); sigma1 = sigma
        Y = matvec(X); Y -= c * X; Y *= (sigma1 / e); nmv += 1
        for i in range(2, deg + 1):
            sigma_new = 1.0 / (2.0 / sigma1 - sigma)
            Z = matvec(Y); Z -= c * Y; Z *= (2.0 * sigma_new / e); Z -= (sigma * sigma_new) * X; nmv += 1
            X = Y; Y = Z; del Z; sigma = sigma_new
        del X
        X, HX, th, res, orth = rr(Y); nmv += 1
        del HX
        lam_min_est = min(lam_min_est, float(th[0]))
        worstK = float(res[:K].max())
        history.append({'pass': p, 'deg': deg, 'theta_1': float(th[0]), 'theta_K': float(th[K-1]), 'theta_m': float(th[-1]),
                        'resK_max': worstK, 'resK_min': float(res[:K].min()), 'matvecs': nmv, 'time_s': time.time() - t0, 'orth_err': orth})
        if logf is not None:
            log(f"   pass {p:3d} deg {deg:3d} nmv {nmv:5d}  theta_1={th[0]:.7f} theta_K={th[K-1]:.7f} theta_m={th[-1]:.7f}  "
                f"res[:K] max={worstK:.2e} min={res[:K].min():.2e} res[K:] min={res[K:].min() if m > K else float('nan'):.2e} orth={orth:.1e}  "
                f"{time.time()-t0:.0f}s rss={maxrss_gb():.2f}GB", logf)
        if worstK < tol: break
        if time.time() - t0 > time_budget:
            if logf is not None: log("   time budget exhausted", logf)
            break
        deg = min(deg_max, int(deg * 1.5) if p > 0 and worstK > 1e-2 else deg + 10)
    return th, X, res, nmv, history

def lobpcg_lowest(matvec, N, diag, k=6, seed=0, maxiter=4000, tol=1e-7):
    """Matrix-free LOBPCG with diagonal preconditioner, as in audit/phase5_bulk_bottom_lobpcg.py (seed 0)."""
    rng = np.random.default_rng(seed)
    X = rng.standard_normal((N, k)) + 1j * rng.standard_normal((N, k))
    H = spl.LinearOperator((N, N), matvec=lambda v: matvec(v.reshape(N, -1)).reshape(v.shape), matmat=lambda V: matvec(V), dtype=complex)
    dinv = 1.0 / diag
    M = spl.LinearOperator((N, N), matvec=lambda v: (dinv * v.reshape(N, -1).T).T.reshape(v.shape), dtype=complex)
    import warnings
    with warnings.catch_warnings(record=True) as wlist:
        warnings.simplefilter("always")
        w, V = spl.lobpcg(H, X, M=M, largest=False, tol=tol, maxiter=maxiter)
    o = np.argsort(w.real); w = w.real[o]; V = V[:, o]
    V = V / np.linalg.norm(V, axis=0)
    res = np.linalg.norm(matvec(V) - V * w[None, :], axis=0)
    return w, V, res, [str(x.message)[:200] for x in wlist]

# ----------------------------------------------------------------------------------------------------------------
# Diagnostics
# ----------------------------------------------------------------------------------------------------------------
def tile_weights(psi, n, spinor=True):
    if spinor:
        p = np.abs(psi[0::2]) ** 2 + np.abs(psi[1::2]) ** 2
    else:
        p = np.abs(psi) ** 2
    return p / p.sum()

def diagnostics(p, patch):
    L, n = patch.level, patch.n
    ipr = float((p ** 2).sum()); ipr3 = float((p ** 3).sum())
    out = {'ipr': ipr, 'P': 1.0 / ipr, 'ipr_n': ipr * n, 'ipr_q3': ipr3,
           'boundary_weight': float(p[patch.boundary].sum()),
           'interface_weight': {str(d): float(p[patch.interface[d]].sum()) for d in range(1, L + 1)},
           'box_S2': [], 'box_S3': [], 'child_weights_depth1': None}
    for d in range(0, L + 1):
        q = 8 ** (L - d)
        W = p.reshape(8 ** d, q).sum(axis=1)   # weight in each level-(L-d) child (contiguous blocks in depth-first order)
        out['box_S2'].append(float((W ** 2).sum())); out['box_S3'].append(float((W ** 3).sum()))
        if d == 1: out['child_weights_depth1'] = [float(x) for x in W]
    return out

def summarize_block(w, V, res, patch, spinor=True, nmax=None):
    recs = []
    nmax = len(w) if nmax is None else min(nmax, len(w))
    for i in range(nmax):
        p = tile_weights(V[:, i], patch.n, spinor)
        rec = {'index': i, 'eigenvalue': float(w[i]), 'residual': float(res[i])}
        rec.update(diagnostics(p, patch))
        recs.append(rec)
    return recs

def average_profile(recs, patch, idx):
    """Averaged (over eigenvectors idx) quantities: mean IPR, IPR of the averaged weight, mean interface profile."""
    iprs = np.array([recs[i]['ipr'] for i in idx])
    return {'indices': list(map(int, idx)), 'mean_ipr': float(iprs.mean()), 'mean_ipr_n': float(iprs.mean() * patch.n),
            'mean_P': float((1 / iprs).mean()), 'mean_boundary_weight': float(np.mean([recs[i]['boundary_weight'] for i in idx])),
            'mean_interface_weight': {str(d): float(np.mean([recs[i]['interface_weight'][str(d)] for i in idx])) for d in range(1, patch.level + 1)},
            'mean_box_S2': [float(np.mean([recs[i]['box_S2'][d] for i in idx])) for d in range(patch.level + 1)]}

# ----------------------------------------------------------------------------------------------------------------
def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--level', type=int, required=True)
    ap.add_argument('--K', type=int, default=128)
    ap.add_argument('--extra', type=int, default=64, help='extra block vectors for the Chebyshev solver (m = K + extra)')
    ap.add_argument('--deg-max', type=int, default=80)
    ap.add_argument('--free-block', type=int, default=0, help='block size for the free-operator ChebFSI (default max(32, 4*Kfree))')
    ap.add_argument('--tol', type=float, default=1e-7)
    ap.add_argument('--time-budget', type=float, default=1500.0)
    ap.add_argument('--Kfree', type=int, default=8)
    ap.add_argument('--Ktriv', type=int, default=8)
    ap.add_argument('--skip-lobpcg', action='store_true')
    ap.add_argument('--skip-controls', action='store_true')
    ap.add_argument('--out', default=None)
    ap.add_argument('--validate-chebfsi', action='store_true', help='at dense levels also run the Chebyshev solver and compare')
    ap.add_argument('--builder', default='objects', choices=['objects', 'grid'])
    ap.add_argument('--skip-free', action='store_true')
    ap.add_argument('--lobpcg-maxiter', type=int, default=4000)
    ap.add_argument('--trivial-only-pinned', action='store_true')
    args = ap.parse_args()
    L, K = args.level, args.K
    outdir = os.path.join(HERE, 'results'); os.makedirs(outdir, exist_ok=True)
    tag = args.out or f'phase5a_edge_states_level{L}'
    fh = open(os.path.join(outdir, tag + '.txt'), 'w')
    T0 = time.time()
    patch = Patch(L, args.builder); n = patch.n; N = 2 * n
    log(f"level {L} (builder {args.builder}): n={n} tiles, dim={N}, panels={len(patch.ea)}, boundary tiles={int(patch.boundary.sum())}, "
        f"interface tiles by depth {{d: |I_d|}} = { {d: int(patch.interface[d].sum()) for d in range(1, L+1)} }, "
        f"link labels {patch.label_counts}, build {patch.build_time:.1f}s rss={maxrss_gb():.2f}GB", fh)
    result = {'level': L, 'n': n, 'dim': N, 'n_panels': int(len(patch.ea)), 'n_boundary_tiles': int(patch.boundary.sum()),
              'interface_tile_counts': {str(d): int(patch.interface[d].sum()) for d in range(1, L + 1)},
              'link_label_counts': patch.label_counts, 'K': K, 'tol': args.tol,
              'ipr_definition': 'p_a = |psi[2a]|^2 + |psi[2a+1]|^2 (sum 1); IPR = sum p_a^2; P = 1/IPR; uniform over n tiles -> 1/n'}
    # exact operators and verification
    Hpin = patch.sparse_H(True); Hfree = patch.sparse_H(False)
    mv_pin = lambda X: Hpin @ X; mv_free = lambda X: Hfree @ X
    dpin = np.full(n, 24.0)
    herm = abs(Hpin - Hpin.conj().T).max()
    Href = patch.reference_H(True)
    ref_err = float(abs(Hpin - Href).max()) if Href is not None else None
    del Href
    diag_err = abs((Hpin - Hfree) - sps.diags(np.repeat(24.0 - patch.deg, 2))).max()
    log(f"operator checks: nnz(H_pin)={Hpin.nnz}, hermiticity max|H-H^+|={herm:.1e}, max|H_pin - per-edge reference| = {ref_err}, "
        f"H_pin - H_free = diag(24-deg): {diag_err:.1e}", fh)
    assert herm < 1e-12 and diag_err < 1e-12 and (ref_err is None or ref_err < 1e-12)
    result['checks'] = {'nnz_Hpin': int(Hpin.nnz), 'hermiticity': float(herm), 'reference_construction_maxdiff': ref_err, 'builder': args.builder}
    if args.builder == 'grid' and L <= 5:
        t1 = time.time(); P2 = Patch(L, 'objects')
        same = np.array_equal(patch.canonical_edge_multiset(), P2.canonical_edge_multiset()) and np.array_equal(patch.deg, P2.deg) and np.array_equal(patch.fid, P2.fid)
        log(f"builder cross-validation grid vs objects at level {L}: identical edge multiset, labels, degrees, frames = {same} ({time.time()-t1:.0f}s)", fh)
        result['checks']['grid_vs_objects_identical'] = bool(same); assert same; del P2
    dense = N <= 8192

    # ---------------- pinned Clifford: lowest K ----------------
    t0 = time.time()
    if dense:
        w, V = dense_lowest(Hpin, K); res = np.linalg.norm(Hpin @ V - V * w[None, :], axis=0)
        solver = 'dense scipy.linalg.eigh (driver evr, subset_by_index)'
        nmv = None; hist = None
        log(f"H_pin dense: lowest {np.round(w[:6], 6)}  max residual (K={K}) {res.max():.2e}  ({time.time()-t0:.0f}s, rss={maxrss_gb():.2f}GB)", fh)
    else:
        m = K + args.extra
        log(f"H_pin Chebyshev-filtered subspace iteration: K={K}, block m={m}, lam_max=48, tol={args.tol}", fh)
        th, X, resm, nmv, hist = chebfsi(mv_pin, N, K, m, 48.0, tol=args.tol, time_budget=args.time_budget, logf=fh, deg_max=args.deg_max)
        w, V, res = th[:K], X[:, :K], resm[:K]
        # exact residual recheck with the sparse matrix
        res_exact = np.linalg.norm(Hpin @ V - V * w[None, :], axis=0)
        log(f"H_pin ChebFSI: lowest {np.round(w[:6], 6)}  residuals (exact sparse) max {res_exact.max():.2e} min {res_exact.min():.2e}; "
            f"|res_fast - res_sparse| max {abs(res - res_exact).max():.1e}; matvecs {nmv} ({time.time()-t0:.0f}s, rss={maxrss_gb():.2f}GB)", fh)
        res = res_exact
        solver = f'Chebyshev-filtered subspace iteration (block {m}, {nmv} block matvecs) + Rayleigh-Ritz'
    if dense and args.validate_chebfsi:
        t1 = time.time(); m = K + args.extra
        thv, Xv, resv, nmvv, _ = chebfsi(mv_pin, N, K, m, 48.0, tol=args.tol, time_budget=args.time_budget, logf=fh)
        dev = abs(thv[:K] - w).max(); resv_exact = np.linalg.norm(Hpin @ Xv[:, :K] - Xv[:, :K] * thv[None, :K], axis=0)
        # subspace agreement: principal angles between the lowest-K dense and Chebyshev subspaces
        sv = np.linalg.svd(V.conj().T @ Xv[:, :K], compute_uv=False)
        log(f"VALIDATION dense vs ChebFSI (K={K}, block {m}, {nmvv} matvecs, {time.time()-t1:.0f}s): max|lambda_dense - lambda_cheb| = {dev:.2e}, "
            f"Cheb residuals max {resv_exact.max():.1e}, min singular value of <V_dense|V_cheb> = {sv.min():.6f} (1 = identical subspaces)", fh)
        pv = tile_weights(Xv[:, 0], n); pd = tile_weights(V[:, 0], n)
        log(f"   ground-state IPR*n dense {float((pd**2).sum())*n:.4f} vs ChebFSI {float((pv**2).sum())*n:.4f}", fh)
        result['validation_chebfsi'] = {'max_eigenvalue_deviation': float(dev), 'cheb_residual_max': float(resv_exact.max()), 'min_sv_subspace_overlap': float(sv.min()),
                                        'ground_ipr_n_dense': float((pd**2).sum())*n, 'ground_ipr_n_cheb': float((pv**2).sum())*n, 'matvecs': nmvv}
        del Xv
    recs = summarize_block(w, V, res, patch)
    result['pinned'] = {'solver': solver, 'eigenpairs': recs, 'lowest_eigenvalue': float(w[0]), 'lowest_residual': float(res[0]),
                        'avg_lowest8': average_profile(recs, patch, range(min(8, K))), 'avg_all': average_profile(recs, patch, range(K)),
                        'time_s': time.time() - t0, 'chebfsi_history': hist}
    gaps = np.diff(w)
    log(f"H_pin: lambda_1..8 = {np.round(w[:8], 6).tolist()}; lambda_K={w[K-1]:.6f}; Kramers pairing max|l_2j-l_2j-1| = {max(abs(w[1::2]-w[0::2][:len(w[1::2])])):.1e}; "
        f"min gap between consecutive doublets {gaps[1::2].min():.2e}", fh)
    for r in recs[:8]:
        log(f"   #{r['index']:3d} lambda={r['eigenvalue']:.7f} res={r['residual']:.1e} IPR={r['ipr']:.6f} IPR*n={r['ipr_n']:.3f} P={r['P']:.1f} bw={r['boundary_weight']:.4f} "
            f"interface w(d)={ {d: round(v, 4) for d, v in r['interface_weight'].items()} }  S2(d)={np.round(r['box_S2'], 4).tolist()}", fh)
    ap8 = result['pinned']['avg_lowest8']
    log(f"   avg lowest 8: mean IPR*n={ap8['mean_ipr_n']:.3f}, mean boundary weight={ap8['mean_boundary_weight']:.4f}, interface {ap8['mean_interface_weight']}, "
        f"tile fractions {{d: |I_d|/n}} = { {d: round(int(patch.interface[d].sum())/n, 4) for d in range(1, L+1)} }", fh)
    del V

    # ---------------- LOBPCG cross-check of the pinned bottom (previous approach) ----------------
    if not args.skip_lobpcg:
        t0 = time.time()
        wl, Vl, rl, warns = lobpcg_lowest(mv_pin, N, np.repeat(dpin, 2), k=6, seed=0, maxiter=args.lobpcg_maxiter, tol=1e-7)
        p = tile_weights(Vl[:, 0], n)
        log(f"H_pin LOBPCG(k=6, seed 0) cross-check: {np.round(wl, 6).tolist()} residuals {['%.1e' % x for x in rl]} ground-state IPR*n={float((p**2).sum())*n:.3f} "
            f"({time.time()-t0:.0f}s) warnings: {warns[:1]}", fh)
        result['pinned']['lobpcg_crosscheck'] = {'eigenvalues': wl.tolist(), 'residuals': rl.tolist(), 'ground_ipr_n': float((p**2).sum()) * n, 'time_s': time.time() - t0, 'warnings': warns}
        del Vl

    # ---------------- free Clifford: lowest Kfree (surface band) ----------------
    t0 = time.time(); Kf = args.Kfree
    if args.skip_free:
        pass
    elif dense:
        wf, Vf = dense_lowest(Hfree, Kf); rf = np.linalg.norm(Hfree @ Vf - Vf * wf[None, :], axis=0); sol = 'dense eigh subset'; nmvf = None
    else:
        mf = args.free_block or max(32, 4 * Kf)
        thf, Xf, rmf, nmvf, _ = chebfsi(mv_free, N, Kf, mf, 48.0, tol=args.tol, time_budget=600.0, logf=fh, seed=1)
        wf, Vf = thf[:Kf], Xf[:, :Kf]; rf = np.linalg.norm(Hfree @ Vf - Vf * wf[None, :], axis=0); sol = f'ChebFSI block {mf}, {nmvf} matvecs'
    if args.skip_free:
        log("H_free: skipped", fh); recf = None
    else:
      recf = summarize_block(wf, Vf, rf, patch)
      result['free'] = {'solver': sol, 'eigenpairs': recf, 'lowest_eigenvalue': float(wf[0]), 'lowest_residual': float(rf[0]),
                      'avg_lowest8': average_profile(recf, patch, range(min(8, Kf))), 'time_s': time.time() - t0}
      log(f"H_free: lowest {np.round(wf, 6).tolist()} residuals max {rf.max():.1e}  ({time.time()-t0:.0f}s)", fh)
      for r in recf[:4]:
        log(f"   #{r['index']:3d} lambda={r['eigenvalue']:.7f} res={r['residual']:.1e} IPR={r['ipr']:.6f} IPR*n={r['ipr_n']:.3f} P={r['P']:.1f} boundary weight={r['boundary_weight']:.4f} "
            f"interface w(d)={ {d: round(v, 4) for d, v in r['interface_weight'].items()} }", fh)
      log(f"   avg lowest {min(8,Kf)}: mean IPR*n={result['free']['avg_lowest8']['mean_ipr_n']:.3f}, mean boundary weight={result['free']['avg_lowest8']['mean_boundary_weight']:.4f} "
        f"(boundary tile fraction {int(patch.boundary.sum())/n:.4f})", fh)
      del Vf

    # ---------------- trivial connection control (pinned and free), tile operator ----------------
    if not args.skip_controls:
        for pinned in ((True,) if args.trivial_only_pinned else (True, False)):
            t0 = time.time(); Kt = args.Ktriv
            Ht = patch.sparse_tile_H(pinned)
            if n <= 8192:
                wt, Vt = sla.eigh(Ht.toarray(), subset_by_index=(0, Kt - 1), driver='evr'); solt = 'dense eigh subset (n x n tile operator)'
            else:
                mvt = lambda X: Ht @ X
                tht, Xt_, rmt, nmvt, _ = chebfsi(mvt, n, Kt, max(32, 4 * Kt), 48.0, tol=args.tol, time_budget=600.0, logf=fh, seed=2, dtype=float)
                wt, Vt = tht[:Kt], Xt_[:, :Kt]; solt = f'ChebFSI real block {max(32, 4*Kt)}, {nmvt} matvecs (n x n tile operator)'
            rt = np.linalg.norm(Ht @ Vt - Vt * wt[None, :], axis=0)
            rect = summarize_block(wt, Vt, rt, patch, spinor=False)
            key = 'trivial_pinned' if pinned else 'trivial_free'
            result[key] = {'solver': solt + '; H_trivial = (this) (x) I_2, each eigenvalue doubly degenerate', 'eigenpairs': rect,
                           'lowest_eigenvalue': float(wt[0]), 'lowest_residual': float(rt[0]), 'avg_lowest8': average_profile(rect, patch, range(min(8, Kt))), 'time_s': time.time() - t0}
            log(f"trivial {'pinned' if pinned else 'free'} (tile operator): lowest {np.round(wt, 6).tolist()} residuals max {rt.max():.1e} ({time.time()-t0:.0f}s)", fh)
            for r in rect[:3]:
                log(f"   #{r['index']:3d} lambda={r['eigenvalue']:.7f} res={r['residual']:.1e} IPR={r['ipr']:.6f} IPR*n={r['ipr_n']:.3f} P={r['P']:.1f} bw={r['boundary_weight']:.4f} "
                    f"interface w(d)={ {d: round(v, 4) for d, v in r['interface_weight'].items()} } S2(d)={np.round(r['box_S2'], 4).tolist()}", fh)
            del Vt
    result['total_time_s'] = time.time() - T0; result['max_rss_gb'] = maxrss_gb()
    with open(os.path.join(outdir, tag + '.json'), 'w') as f: json.dump(result, f, indent=1)
    log(f"saved {os.path.join(outdir, tag + '.json')}  total {time.time()-T0:.0f}s  max rss {maxrss_gb():.2f} GB", fh)
    fh.close()

if __name__ == '__main__':
    main()
