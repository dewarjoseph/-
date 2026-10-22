"""Phase V-E (exploratory): level-7-dependent closure numbers recomputed with the CONVERGED level-7 vector. Usage: python -u -I audit/phase5e_closure_converged.py"""
# recompute the level-7-dependent closure numbers with the CONVERGED level-7 vector (snapshot statistics, transfers, level-5 edges)
import sys, os, json, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np, phase5e_run as R, phase5e_rg as rg, phase5d_schur as d
from independent_clifford_q8_audit import FR30
vecs = R.fr30_vectors(); tiles = d.tiles_of(FR30, 3); _, edges = d.build(tiles); deg = d.degrees(len(tiles), edges); sf = np.nonzero(deg < 24)[0]
X = {}
for L, v in vecs.items():
    v = np.array(v, complex); v /= np.linalg.norm(v); Y = R.snapshots(v, L, 3, sf); X[L] = Y / np.linalg.norm(Y)
out = {'note': 'recomputed with the converged level-7 vector (residual 1.0e-8)', 'cumulative': {}, 'per_level7': {}, 'transfer': {}, 'level5_edge': []}
Ls = sorted(X)
for j in range(1, len(Ls) + 1):
    sv = np.linalg.svd(np.hstack([X[L] for L in Ls[:j]]), compute_uv=False); e = np.cumsum(sv**2) / (sv**2).sum()
    out['cumulative'][''.join(map(str, Ls[:j]))] = {str(f): int(np.searchsorted(e, f) + 1) for f in (0.9, 0.99, 0.999)}
sv = np.linalg.svd(X[7], compute_uv=False); e = np.cumsum(sv**2) / (sv**2).sum(); out['per_level7'] = {str(f): int(np.searchsorted(e, f) + 1) for f in (0.9, 0.99, 0.999)}
cap = lambda U, Y: float(np.linalg.norm(U.conj().T @ Y)**2 / np.linalg.norm(Y)**2)
for tr in ([4, 5], [6], [4, 5, 6], [5, 6]):
    U = np.linalg.svd(np.hstack([X[L] for L in tr]), full_matrices=False)[0]
    out['transfer']['train' + ''.join(map(str, tr)) + '_test7'] = {str(dd): cap(U[:, :dd], X[7]) for dd in (20, 41, 57, 114)}
print(json.dumps(out, indent=0)[:1500], flush=True)
s5 = rg.System(FR30, 5, depth=2); E0 = 8.797011314651467
for tr in ([6, 7], [7]):
    U = np.linalg.svd(np.hstack([X[L] for L in tr]), full_matrices=False)[0]
    for dd in (42, 58):
        red = rg.Reduced(s5, [U[:, :dd].copy() for _ in range(64)]); E, _ = red.root()
        out['level5_edge'].append({'train': tr, 'd': dd, 'D': red.D, 'D_frac': red.D / s5.offs[-1], 'err': E - E0}); print(out['level5_edge'][-1], flush=True)
json.dump(out, open('audit/results/phase5e_closure_converged_L7.json', 'w'), indent=1)
