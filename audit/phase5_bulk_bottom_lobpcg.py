"""
Bulk spectral infimum bracket: lowest eigenvalues of the PINNED Clifford hopping operator (bulk coordination 24 on
every tile; a compression of the infinite bulk operator, so its bottom decreases monotonically to the bulk infimum)
at levels 4..6 by matrix-free LOBPCG with a diagonal preconditioner.  Also recomputes the free level-5 bottom as a
cross-check against the shift-invert value 5.24993.
Run from the repository root:  python3 -u -I audit/phase5_bulk_bottom_lobpcg.py [maxlevel]
"""
import os, sys, time, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np, scipy.sparse as sps, scipy.sparse.linalg as spl
from independent_clifford_q8_audit import FR30, tiles_at_level, panel_edges, clifford_link

maxlvl = int(sys.argv[1]) if len(sys.argv) > 1 else 6
def build(lvl, pinned):
    tiles = tiles_at_level(FR30, lvl); owner, edges = panel_edges(tiles); n = len(tiles)
    deg = collections.Counter()
    for a, b, _, _, _ in edges: deg[a] += 1; deg[b] += 1
    rows, cols, vals = [], [], []
    for a in range(n):
        d = 24.0 if pinned else float(deg[a])
        for r in range(2): rows.append(2*a+r); cols.append(2*a+r); vals.append(d)
    cache = {}
    for (a, b, nf, _, _) in edges:
        key = (a, b, int(np.argmax(nf)))
        C = cache.get(key)
        if C is None: C = clifford_link(tiles[a][0], tiles[b][0], nf); cache[key] = C
        for r in range(2):
            for c in range(2): rows += [2*a+r, 2*b+c]; cols += [2*b+c, 2*a+r]; vals += [-C[r, c], -np.conj(C[r, c])]
    H = sps.coo_matrix((vals, (rows, cols)), shape=(2*n, 2*n)).tocsr()
    nb = sum(1 for a in range(n) if deg[a] < 24)
    return H, n, nb, deg
def lowest(H, k=6, seed=0, maxiter=4000, tol=1e-7):
    rng = np.random.default_rng(seed); N = H.shape[0]
    X = rng.standard_normal((N, k)) + 1j * rng.standard_normal((N, k))
    dinv = 1.0 / H.diagonal().real
    M = spl.LinearOperator(H.shape, matvec=lambda v: dinv * v, dtype=complex)
    w, V = spl.lobpcg(H, X, M=M, largest=False, tol=tol, maxiter=maxiter)
    o = np.argsort(w.real); return w.real[o], V[:, o]
for lvl in range(4, maxlvl + 1):
    for pinned in ([True] if lvl != 5 else [False, True]):
        t0 = time.time(); H, n, nb, deg = build(lvl, pinned)
        w, V = lowest(H)
        psi = V[:, 0]; wt = np.abs(psi[0::2])**2 + np.abs(psi[1::2])**2; wt /= wt.sum()
        bw = float(sum(wt[a] for a in range(n) if deg[a] < 24)); ipr = float((wt**2).sum())
        print(f"level {lvl} dim {H.shape[0]:7d} {'pinned' if pinned else 'free  '}: lowest {np.round(w[:4],5)}  IPR_tiles={ipr:.5f} (1/n={1/n:.6f})  "
              f"boundary tiles {nb}/{n}={nb/n:.3f}  ground-state boundary weight={bw:.3f}  ({time.time()-t0:.0f}s)", flush=True)
