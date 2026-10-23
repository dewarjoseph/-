#!/usr/bin/env python3
"""Phase VIII (section 6): is the edge-selecting configuration a property of the geometry/hierarchy or of the connection?

Same 72 legal FR30 1-star patches sigma^m(tau) (same tiling), different link variables on them:
  FR30      Clifford Q8 links (non-Abelian)
  chi1/2/3  Abelian shadows chi_k o U_FR30 (characters Q8 -> {+-1}); same geometry, same hierarchy, Abelianised flux
  Z2        reflection-only Clifford links are NOT defined on FR30 patches (different frames); omitted
For each system and m = 1..3: U_m(tau) = lambda_min of the pinned patch operator for every tau, and the argmin set.
Usage: python -u -I audit/phase8_selection_controls.py -> audit/results/phase8_selection_controls.json"""
import os, sys, json, time
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); RES = os.path.join(HERE, 'results')
import numpy as np, scipy.sparse as sps, scipy.sparse.linalg as sla
import phase7_local as P
import phase7_adversarial as A
from phase8_patch_bounds import types_sorted
T0 = time.time()
def log(*a): print(f"[{time.time()-T0:7.0f}s]", *a, flush=True)
QIDX = np.array([[[A.link_q(P.Gs[a], P.Gs[b], ax) for ax in range(3)] for b in range(P.NG)] for a in range(P.NG)], np.int8)
CHI = {k: np.array([1 if (e // 2) in (0, k) else -1 for e in range(8)]) for k in (1, 2, 3)}

def patch_operator_chi(poses, chi=None):
    G = np.array([g for g, t in poses], np.int64); T = np.array([t for g, t in poses], np.int64); n = len(G)
    cubes = P.cubes_of_poses(G, T); lo = cubes.reshape(-1, 3).min(0); shp = cubes.reshape(-1, 3).max(0) - lo + 2
    grid = np.full(tuple(shp), -1, np.int64); cc = cubes.reshape(-1, 3) - lo; grid[cc[:, 0], cc[:, 1], cc[:, 2]] = np.repeat(np.arange(n), 7)
    fi = P.frame_index(G); rows, cols, vals = [], [], []
    for ax in range(3):
        sa = [slice(None)] * 3; sb = [slice(None)] * 3; sa[ax] = slice(0, shp[ax] - 1); sb[ax] = slice(1, shp[ax])
        a, b = grid[tuple(sa)].ravel(), grid[tuple(sb)].ravel(); m = (a >= 0) & (b >= 0) & (a != b); a, b = a[m], b[m]
        q = QIDX[fi[a], fi[b], ax]
        if chi is None: C = np.array(A.MAT)[q]
        else: C = CHI[chi][q][:, None, None] * np.eye(2)[None]
        for i in range(2):
            for j in range(2):
                v = C[:, i, j]; nz = np.abs(v) > 0.5
                rows += [2 * a[nz] + i, 2 * b[nz] + j]; cols += [2 * b[nz] + j, 2 * a[nz] + i]; vals += [-v[nz], -np.conj(v[nz])]
    d_ = np.arange(2 * n); rows.append(d_); cols.append(d_); vals.append(np.full(2 * n, 24.0 + 0j))
    return sps.csr_matrix((np.concatenate(vals), (np.concatenate(rows), np.concatenate(cols))), shape=(2 * n, 2 * n))

if __name__ == '__main__':
    Ts = types_sorted(); out = {}
    for name, chi in (('FR30', None), ('chi1', 1), ('chi2', 2), ('chi3', 3)):
        out[name] = {}
        for m in (1, 2, 3):
            vals = []
            for j, tau in enumerate(Ts):
                poses, c = P.poses_from_key(tau)
                for _ in range(m): poses = P.inflate(poses)
                H = patch_operator_chi(poses, chi)
                vals.append(float(sla.eigsh(H, k=2, which='SA', tol=1e-11, ncv=40, return_eigenvectors=False).min()))
            order = np.argsort(vals); out[name][m] = {'argmin': [int(x) for x in order[:6]], 'values': [round(vals[x], 7) for x in order[:6]], 'all': vals}
            log(f"{name} m={m}: U_m = {vals[order[0]]:.6f} at types {order[:6].tolist()} {[round(vals[x], 6) for x in order[:6]]}")
        json.dump(out, open(os.path.join(RES, 'phase8_selection_controls.json'), 'w'), indent=1)
