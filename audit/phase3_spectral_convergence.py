"""
Spectral-measure convergence of the Clifford hopping operator across the hierarchy, with matched controls.
Run from the repository root:  python3 -I audit/phase3_spectral_convergence.py [maxlevel]
"""
import os, sys, collections, itertools, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np, scipy.sparse as sps, scipy.sparse.linalg as spl
from independent_clifford_q8_audit import U3, FR30, perm_mat, tiles_at_level, panel_edges, clifford_link, q8label, SIG

maxlvl = int(sys.argv[1]) if len(sys.argv) > 1 else 4
Q8 = [np.eye(2, dtype=complex), -np.eye(2, dtype=complex)] + [s * 1j * SIG[k] for k in range(3) for s in (1, -1)]
rng = np.random.default_rng(2026)
perms = list(itertools.permutations(range(3)))
even = [p for p in perms if round(np.linalg.det(perm_mat(p))) == 1]; odd = [p for p in perms if round(np.linalg.det(perm_mat(p))) == -1]
def random_decoration(r):
    fr = {'0': even[r.integers(3)]}
    for v in U3: fr[v] = (even if sum(v) % 2 == 0 else odd)[r.integers(3)]
    return fr
RANDDEC = random_decoration(np.random.default_rng(7))

def hopping(n, edges, links):
    rows, cols, vals = [], [], []
    for (a, b, _, _, _), C in zip(edges, links):
        for r in range(2):
            rows += [2*a+r, 2*b+r]; cols += [2*a+r, 2*b+r]; vals += [1.0, 1.0]
            for c in range(2):
                rows += [2*a+r, 2*b+c]; cols += [2*b+c, 2*a+r]; vals += [-C[r, c], -np.conj(C[r, c])]
    return sps.coo_matrix((vals, (rows, cols)), shape=(2*n, 2*n)).tocsr()

def model_links(name, tiles, edges):
    if name == 'clifford':   return [clifford_link(tiles[a][0], tiles[b][0], nf) for a, b, nf, _, _ in edges]
    if name == 'trivial':    return [np.eye(2, dtype=complex)] * len(edges)
    if name == 'randomQ8':   # i.i.d. Q8 links on the same graph (seeded)
        r = np.random.default_rng(11); return [Q8[r.integers(8)] for _ in edges]
    if name == 'adjointonly':  # strip the central sign: project each link to its V4 class representative (+1 or +i sigma_k)
        L = [clifford_link(tiles[a][0], tiles[b][0], nf) for a, b, nf, _, _ in edges]
        return [C if q8label(C)[0] == '+' else -C for C in L]
    raise ValueError

def kolmogorov(ev1, ev2, grid):
    F1 = np.searchsorted(np.sort(ev1), grid, side='right') / len(ev1)
    F2 = np.searchsorted(np.sort(ev2), grid, side='right') / len(ev2)
    return float(np.abs(F1 - F2).max())

grid = np.linspace(-0.5, 30, 6001)
spectra = collections.defaultdict(dict)
for lvl in range(1, maxlvl + 1):
    t0 = time.time()
    tiles = tiles_at_level(FR30, lvl); owner, edges = panel_edges(tiles); n = len(tiles)
    tilesR = tiles_at_level(RANDDEC, lvl); ownerR, edgesR = panel_edges(tilesR)
    for name in ('clifford', 'trivial', 'randomQ8', 'adjointonly'):
        H = hopping(n, edges, model_links(name, tiles, edges))
        spectra[name][lvl] = np.linalg.eigvalsh(H.toarray()) if 2*n <= 8192 else None
    H = hopping(n, edgesR, model_links('clifford', tilesR, edgesR)); spectra['randdecoration'][lvl] = np.linalg.eigvalsh(H.toarray()) if 2*n <= 8192 else None
    print(f"level {lvl}: dim={2*n}  ({time.time()-t0:.0f}s)")
    for name in spectra:
        ev = spectra[name][lvl]
        if ev is not None:
            print(f"   {name:15s} lowest 4 = {np.round(ev[:4],5)}  mean={ev.mean():.4f}  max={ev[-1]:.4f}")

print("\nKOLMOGOROV DISTANCE BETWEEN SUCCESSIVE NORMALIZED SPECTRAL MEASURES (IDS)")
for name in spectra:
    ds = [kolmogorov(spectra[name][l], spectra[name][l+1], grid) for l in range(1, maxlvl) if spectra[name][l+1] is not None]
    print(f" {name:15s}: d_K(N_k, N_(k+1)) for k=1..: {np.round(ds,4)}  ratios: {np.round(np.array(ds[1:])/np.array(ds[:-1]),3)}")
print("\nDISTANCE BETWEEN MODELS AT THE LARGEST LEVEL")
names = list(spectra); L = maxlvl
for a, b in itertools.combinations(names, 2):
    print(f" d_K({a}, {b}) at level {L}: {kolmogorov(spectra[a][L], spectra[b][L], grid):.4f}")

print("\nPERSISTENT SPECTRAL GAPS (relative width > 0.02*spectral range) AND IDS VALUES AT THE GAPS")
def gaps(ev, rel=0.02):
    ev = np.sort(ev); rng_ = ev[-1] - ev[0]; out = []
    for i in range(len(ev) - 1):
        if ev[i+1] - ev[i] > rel * rng_: out.append((round(ev[i], 4), round(ev[i+1], 4), (i + 1) / len(ev)))
    return out
for name in ('clifford', 'trivial', 'adjointonly', 'randomQ8', 'randdecoration'):
    print(f" {name}:")
    for lvl in range(2, maxlvl + 1):
        g = gaps(spectra[name][lvl]); print(f"   level {lvl}: {[(a, b, round(f, 5)) for a, b, f in g][:12]}")

print("\nLOWEST EIGENVALUE SCALING (clifford FR30), including sparse level 5 if feasible")
lows = {l: spectra['clifford'][l][0] for l in range(1, maxlvl + 1)}
try:
    lvl = maxlvl + 1; tiles = tiles_at_level(FR30, lvl); owner, edges = panel_edges(tiles); n = len(tiles)
    H = hopping(n, edges, model_links('clifford', tiles, edges)); t0 = time.time()
    w = spl.eigsh(H, k=4, sigma=-1.0, which='LM', return_eigenvectors=False); lows[lvl] = np.sort(w)[0]
    print(f" level {lvl} (dim {2*n}) lowest 4 via shift-invert: {np.round(np.sort(w),5)} ({time.time()-t0:.0f}s)")
except Exception as e: print(" level", maxlvl + 1, "skipped:", e)
print(" lambda_min by level:", {l: round(float(v), 5) for l, v in lows.items()})
