#!/usr/bin/env python3
"""Phase V-C, checklist items 1 and 2: long-wavelength dispersion and the Kahler-Dirac index on the Chair44/FR30 complex.

PART A (dispersion of the massless operator).  The only gapless operator in the program is the graph Laplacian of the
tile adjacency graph with TRIVIAL links, L = 24 I - A_0 (panel multigraph, 24 panels per tile).  The Q8-decorated operator
is gapped (E_bulk >= 4.008 certified), so it has no long-wavelength branch at all.  On the FR30 periodic approximant of
level k (level-k supertile repeated on the lattice 2^k Lambda_7; audit/phase5a_periodic_approximants.Approximant) the
lowest Bloch band of L is omega^2(q) = q.Dq + Q4(q) + O(q^6).  We extract, along 49 directions, the coefficients of
t^2, t^4 (and t^6) of omega^2(t n) by exact dense diagonalisation and a polynomial fit on t in [0.005, 0.08] (lengths in
unit-cube edges a).  Reported: the 3x3 tensor D (isotropy test), c^2(n) = n.Dn, and alpha(n) = Q4(n)/c^2(n)^2 ... see
`alpha` definition below: with E^2 = c^2 p^2 + c4 p^4, alpha := c4 / c^2 (units a^2), i.e. E^2/c^2 = p^2 + alpha p^4.
A k-sequence shows what survives in the aperiodic limit.

PART B (Kahler-Dirac on the dual cubical complex).  Cells of the level-L patch: 0-cells = unit cubes (7*8^L), 1-cells =
pairs (x, x+e_mu) of present cubes, 2-cells = 2x2 squares of present cubes, 3-cells = 2x2x2 blocks of present cubes
(dual cubical complex; a subcomplex of the dual of Z^3).  Coefficients C^2, parallel transport U(x,mu) = identity if x and
x+e_mu lie in the same tile, else the FR30 Clifford link C_ab = (sigma.M_a^T e_mu)(sigma.M_b^T e_mu).  Covariant
coboundary (standard lattice exterior derivative):
    (d_A w)(x, I) = sum_{mu in I} s(mu, I) [ U(x,mu) w(x+e_mu, I\\mu) - w(x, I\\mu) ],  s = (-1)^{position of mu in I}.
d_A^2 = 0 iff the connection is flat; for FR30 it is not.  D = d_A + d_A^dagger is Hermitian and odd for Gamma = (-1)^deg.
Index theorem used (elementary, any finite complex, any connection): ind(D_+) = dim ker D_+ - dim ker D_+^dagger
= dim C^even - dim C^odd = 2 chi(patch).  We verify it numerically and compute the low spectrum (mass gap).
Usage: python3 -u -I audit/phase5c_dirac.py dispersion <kmax> | dirac <Lmax> | all
"""
import os, sys, time, json, itertools
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
RES = os.path.join(HERE, 'results')
import numpy as np, scipy.sparse as sps, scipy.sparse.linalg as spl, scipy.linalg as sla
from independent_clifford_q8_audit import FR30, tiles_at_level, panel_edges, clifford_link

def log(*a): print(*a, flush=True)

# ------------------------------------------------------------------ PART A
def directions():
    out = []
    for v in itertools.product((-1, 0, 1), repeat=3):
        v = np.array(v, float)
        if v.any() and tuple(-v) not in [tuple(w) for w in out]: out.append(v)   # 13 lattice directions
    rng = np.random.default_rng(20261021)
    for _ in range(36): out.append(rng.normal(size=3))
    return [v / np.linalg.norm(v) for v in out]

def dispersion(kmax):
    import phase5a_periodic_approximants as pa
    res = {}
    ts = np.linspace(0.005, 0.08, 16)
    for k in range(1, kmax + 1):
        t0 = time.time(); A = pa.Approximant(k)
        D = A.D; rows, cols = A.rows, A.cols; n = A.n
        def omega2(q):
            ph = np.exp(1j * (D @ q))
            M = sps.coo_matrix((-ph, (rows, cols)), shape=(n, n)).tocsr() + 24.0 * sps.identity(n, format='csr')
            if n <= 600: return sla.eigvalsh(M.toarray(), subset_by_index=(0, 0))[0]
            return spl.eigsh(M.tocsc(), k=1, sigma=-1e-3, which='LM', return_eigenvectors=False)[0]
        w0 = omega2(np.zeros(3))
        rec = {'k': k, 'n_tiles': n, 'omega2_at_0': float(w0), 'dirs': []}
        # Hessian tensor D from second differences on a basis
        for nv in directions():
            y = np.array([omega2(t * nv) for t in ts]) - w0
            X = np.c_[ts ** 2, ts ** 4, ts ** 6]
            c, *_ = np.linalg.lstsq(X, y, rcond=None); fit_res = float(np.abs(X @ c - y).max())
            rec['dirs'].append({'n': nv.tolist(), 'c2': float(c[0]), 'c4': float(c[1]), 'c6': float(c[2]), 'alpha': float(c[1] / c[0]), 'fit_maxres': fit_res})
        c2 = np.array([d['c2'] for d in rec['dirs']]); al = np.array([d['alpha'] for d in rec['dirs']])
        # least-squares symmetric tensor from c2(n) = n^T D n
        N = np.array([d['n'] for d in rec['dirs']])
        X = np.c_[N[:, 0] ** 2, N[:, 1] ** 2, N[:, 2] ** 2, 2 * N[:, 0] * N[:, 1], 2 * N[:, 0] * N[:, 2], 2 * N[:, 1] * N[:, 2]]
        s, *_ = np.linalg.lstsq(X, c2, rcond=None)
        Dt = np.array([[s[0], s[3], s[4]], [s[3], s[1], s[5]], [s[4], s[5], s[2]]]); ev = np.linalg.eigvalsh(Dt)
        rec.update({'D_tensor': Dt.tolist(), 'D_eigs': ev.tolist(), 'c2_min': float(c2.min()), 'c2_max': float(c2.max()),
                    'c2_anisotropy': float((c2.max() - c2.min()) / c2.mean()), 'alpha_min': float(al.min()), 'alpha_max': float(al.max()),
                    'alpha_mean': float(al.mean()), 'seconds': time.time() - t0})
        log(f"[A k={k}] n={n} omega2(0)={w0:.2e}  D eigs {np.round(ev,4)}  c2 in [{c2.min():.4f},{c2.max():.4f}] (aniso {rec['c2_anisotropy']:.3f})  "
            f"alpha in [{al.min():.4f},{al.max():.4f}] mean {al.mean():.4f}  max fit res {max(d['fit_maxres'] for d in rec['dirs']):.1e}  ({time.time()-t0:.0f}s)")
        res[k] = rec
    # reference: simple cubic lattice Laplacian (exact): omega^2 = sum 4 sin^2(p_i/2) -> c2 = 1, alpha(n) = -(1/12) sum n_i^4
    cub = [{'n': d['n'], 'alpha': -sum(x ** 4 for x in d['n']) / 12} for d in res[1]['dirs']]
    out = {'approximants': res, 'cubic_reference': {'c2': 1.0, 'alpha_min': min(c['alpha'] for c in cub), 'alpha_max': max(c['alpha'] for c in cub)}}
    with open(os.path.join(RES, 'phase5c_dispersion.json'), 'w') as f: json.dump(out, f, indent=1)
    return out

# ------------------------------------------------------------------ PART B
SIG = [np.array([[0, 1], [1, 0]], complex), np.array([[0, -1j], [1j, 0]], complex), np.array([[1, 0], [0, -1]], complex)]
I2 = np.eye(2, dtype=complex)

def complex_cells(L, trivial=False):
    tiles = tiles_at_level(FR30, L); N = 2 ** (L + 1)
    own = -np.ones((N, N, N), int)
    for a, (_, _, cs) in enumerate(tiles):
        for c in cs: own[c] = a
    sites = np.argwhere(own >= 0); sidx = -np.ones((N, N, N), int); sidx[tuple(sites.T)] = np.arange(len(sites))
    E = np.eye(3, dtype=int)
    def present(x): return ((x >= 0) & (x < N)).all(axis=1)
    cells = {0: [(tuple(x), ()) for x in sites]}
    for deg in (1, 2, 3):
        cl = []
        for I in itertools.combinations(range(3), deg):
            ok = np.ones(len(sites), bool)
            for sub in itertools.product((0, 1), repeat=deg):
                y = sites + sum(s * E[m] for s, m in zip(sub, I))
                pr = present(y); ok &= pr
                ok[pr] &= own[tuple(y[pr].T)] >= 0
            cl += [(tuple(x), I) for x in sites[ok]]
        cells[deg] = cl
    index = {deg: {c: i for i, c in enumerate(cells[deg])} for deg in cells}
    def U(x, mu):
        y = np.array(x) + E[mu]; a = own[x]; b = own[tuple(y)]
        if trivial or a == b: return I2
        return clifford_link(tiles[a][0], tiles[b][0], E[mu])
    return tiles, cells, index, U

def coboundary(cells, index, U, deg):
    """matrix of d_A: C^deg (x) C^2 -> C^{deg+1} (x) C^2"""
    rows, cols, vals = [], [], []
    E = np.eye(3, dtype=int)
    for r, (x, I) in enumerate(cells[deg + 1]):
        for pos, mu in enumerate(I):
            s = (-1) ** pos; J = tuple(m for m in I if m != mu)
            y = tuple(np.array(x) + E[mu])
            cy = index[deg][(y, J)]; cx = index[deg][(x, J)]
            Ux = U(x, mu)
            for i in range(2):
                for j in range(2):
                    if Ux[i, j] != 0: rows.append(2 * r + i); cols.append(2 * cy + j); vals.append(s * Ux[i, j])
                rows.append(2 * r + i); cols.append(2 * cx + i); vals.append(-s)
    return sps.coo_matrix((vals, (rows, cols)), shape=(2 * len(cells[deg + 1]), 2 * len(cells[deg]))).tocsr()

def dirac(Lmax):
    out = {}
    for L in range(1, Lmax + 1):
        for conn in ('trivial', 'fr30'):
            t0 = time.time()
            tiles, cells, index, U = complex_cells(L, trivial=(conn == 'trivial'))
            nc = {k: len(v) for k, v in cells.items()}; chi = nc[0] - nc[1] + nc[2] - nc[3]
            d = [coboundary(cells, index, U, k) for k in range(3)]
            curv = [float(abs(d[1] @ d[0]).max()), float(abs(d[2] @ d[1]).max())]
            dims = [2 * nc[k] for k in range(4)]; off = np.cumsum([0] + dims)
            # D_+ : even (0,2) -> odd (1,3); block form [[d0, d1^*],[0, d2]] mapping (w0,w2) -> (w1,w3)
            Dp = sps.bmat([[d[0], d[1].conj().T], [None, d[2]]]).tocsr()          # rows: C1 + C3, cols: C0 + C2
            dimE, dimO = dims[0] + dims[2], dims[1] + dims[3]
            rec = {'L': L, 'connection': conn, 'cells': nc, 'chi': chi, 'curvature_max': curv, 'dim_even': dimE, 'dim_odd': dimO,
                   'index_formula': dimE - dimO}
            if Dp.shape[0] * Dp.shape[1] <= 7000 ** 2:
                s = sla.svdvals(Dp.toarray())               # singular values; ker D_+ = dimE - rank, ker D_+^* = dimO - rank
                tol = 1e-9 * s.max(); rank = int((s > tol).sum())
                pos = np.sort(s[s > tol])
                rec.update({'method': 'dense SVD', 'rank': rank, 'ker_Dplus': dimE - rank, 'ker_Dminus': dimO - rank,
                            'index_numeric': (dimE - rank) - (dimO - rank), 'smallest_nonzero_sv': pos[:6].tolist()})
            else:
                # smallest eigenvalues of the even Hodge Laplacian D_+^* D_+ and odd D_+ D_+^*
                Le = (Dp.conj().T @ Dp).tocsc(); Lo = (Dp @ Dp.conj().T).tocsc()
                ve = spl.eigsh(Le, k=8, sigma=-1e-4, which='LM', return_eigenvectors=False); vo = spl.eigsh(Lo, k=8, sigma=-1e-4, which='LM', return_eigenvectors=False)
                ve, vo = np.sort(ve), np.sort(vo); z = 1e-8
                rec.update({'method': 'shift-invert eigsh (8 lowest each grading)', 'lowest_even_D2': ve.tolist(), 'lowest_odd_D2': vo.tolist(),
                            'ker_Dplus': int((ve < z).sum()), 'ker_Dminus': int((vo < z).sum()),
                            'smallest_nonzero_sv': np.sqrt(np.sort(np.r_[ve[ve >= z], vo[vo >= z]]))[:6].tolist()})
                rec['index_numeric'] = rec['ker_Dplus'] - rec['ker_Dminus']
            # degree-0 Hodge Laplacian = cube-resolved Laplacian; its bottom is the 'mass' of the scalar sector
            L0 = (d[0].conj().T @ d[0]).tocsc()
            v0 = spl.eigsh(L0, k=4, sigma=-1e-4, which='LM', return_eigenvectors=False) if L0.shape[0] > 200 else np.linalg.eigvalsh(L0.toarray())[:4]
            rec['lowest_Delta0'] = np.sort(v0).tolist(); rec['seconds'] = time.time() - t0
            log(f"[B L={L} {conn:7s}] cells {nc} chi={chi}  |d1d0|max={curv[0]:.2f} |d2d1|max={curv[1]:.2f}  dimE-dimO={dimE-dimO}  "
                f"ker D+={rec['ker_Dplus']} ker D-={rec['ker_Dminus']} index={rec['index_numeric']}  smallest nonzero |E| {np.round(rec['smallest_nonzero_sv'][:3],5)}  "
                f"Delta0 bottom {rec['lowest_Delta0'][0]:.5f}  ({rec['seconds']:.0f}s)")
            out[f'{L}_{conn}'] = rec
    with open(os.path.join(RES, 'phase5c_dirac.json'), 'w') as f: json.dump(out, f, indent=1)
    return out

if __name__ == '__main__':
    os.environ.setdefault('OMP_NUM_THREADS', '2')
    cmd = sys.argv[1]
    if cmd in ('dispersion', 'all'): dispersion(int(sys.argv[2]) if len(sys.argv) > 2 else 3)
    if cmd == 'dirac': dirac(int(sys.argv[2]) if len(sys.argv) > 2 else 2)
