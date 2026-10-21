"""
Phase 5 dynamics: is the spectral bottom of the Clifford hopping operator a bulk quantity?
Compares free boundaries (H = D - A, degree-type diagonal) with pinned boundaries (H = 24 - A, every tile given the
bulk coordination 24) at levels 2..5, reports the lowest eigenvalues, the inverse participation ratio of the ground
state on tiles, and its weight on boundary tiles (degree < 24).  Also saves the full level-4 spectra (free/pinned)
for the density-of-states analysis near the bottom.
Run from the repository root:  python3 -u -I audit/phase5_dynamics_boundary.py [maxlevel]
"""
import os, sys, time, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np, scipy.sparse as sps, scipy.sparse.linalg as spl
from independent_clifford_q8_audit import FR30, tiles_at_level, panel_edges, clifford_link, SIG

maxlvl = int(sys.argv[1]) if len(sys.argv) > 1 else 5
Q8 = [np.eye(2, dtype=complex), -np.eye(2, dtype=complex)] + [s * 1j * SIG[k] for k in range(3) for s in (1, -1)]
def hopping(n, edges, links, pinned):
    rows, cols, vals = [], [], []
    deg = collections.Counter()
    for a, b, _, _, _ in edges: deg[a] += 1; deg[b] += 1
    for a in range(n):
        d = 24.0 if pinned else float(deg[a])
        for r in range(2): rows.append(2*a+r); cols.append(2*a+r); vals.append(d)
    for (a, b, _, _, _), C in zip(edges, links):
        for r in range(2):
            for c in range(2):
                rows += [2*a+r, 2*b+c]; cols += [2*b+c, 2*a+r]; vals += [-C[r, c], -np.conj(C[r, c])]
    return sps.coo_matrix((vals, (rows, cols)), shape=(2*n, 2*n)).tocsr(), deg

out = {}
for lvl in range(2, maxlvl + 1):
    tiles = tiles_at_level(FR30, lvl); owner, edges = panel_edges(tiles); n = len(tiles)
    links = {'clifford': [clifford_link(tiles[a][0], tiles[b][0], nf) for a, b, nf, _, _ in edges],
             'trivial': [np.eye(2, dtype=complex)] * len(edges),
             'randomQ8': [Q8[i] for i in np.random.default_rng(11).integers(0, 8, len(edges))]}
    for model in ('clifford', 'trivial', 'randomQ8'):
        for pinned in (False, True):
            H, deg = hopping(n, edges, links[model], pinned); t0 = time.time()
            if 2*n <= 2048:
                w, V = np.linalg.eigh(H.toarray()); w, V = w[:6], V[:, :6]
            else:
                w, V = spl.eigsh(H, k=6, sigma=-1.0 if not pinned else 0.0, which='LM'); o = np.argsort(w); w, V = w[o], V[:, o]
            psi = V[:, 0]; wt = np.abs(psi[0::2])**2 + np.abs(psi[1::2])**2   # tile weights
            ipr = float((wt**2).sum()); nb = sum(1 for a in range(n) if deg[a] < 24)
            bw = float(sum(wt[a] for a in range(n) if deg[a] < 24))
            out[(lvl, model, pinned)] = (w, ipr, bw, nb)
            print(f"level {lvl} dim {2*n:6d} {model:9s} {'pinned' if pinned else 'free  '}: lowest {np.round(w[:4],5)}  IPR_tiles={ipr:.4f} (1/n={1/n:.5f})  "
                  f"boundary tiles {nb}/{n}={nb/n:.3f}  ground-state weight on boundary tiles={bw:.3f}  ({time.time()-t0:.0f}s)", flush=True)
    if lvl == 4:
        for pinned in (False, True):
            H, _ = hopping(n, edges, links['clifford'], pinned); ev = np.linalg.eigvalsh(H.toarray())
            np.save(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'results', f'level4_clifford_{"pinned" if pinned else "free"}_eigs.npy'), ev)
            E0 = ev[0]; print(f"   level-4 {'pinned' if pinned else 'free'} full spectrum saved; IDS near bottom: ", end='')
            for dE in (0.25, 0.5, 1.0, 2.0): print(f"N(E0+{dE})={np.searchsorted(ev, E0+dE)/len(ev):.5f} ", end='')
            print(flush=True)
print("\nSUMMARY lambda_min (free <= bulk infimum <= pinned if the limits coincide):")
for model in ('clifford', 'trivial', 'randomQ8'):
    print(f" {model:9s} free  :", [round(float(out[(l, model, False)][0][0]), 5) for l in range(2, maxlvl + 1)])
    print(f" {model:9s} pinned:", [round(float(out[(l, model, True)][0][0]), 5) for l in range(2, maxlvl + 1)])
