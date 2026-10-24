#!/usr/bin/env python3
"""Phase VIII (section 3/7): can the renormalization state be constructed from LOCAL environments, without solving deeper levels?

Background (Phase V-E, exploratory): the restrictions of the deep FR30 edge states to the surfaces of the level-3 copies span a
local state space that saturates at about 34/56 dimensions (99/99.9 %) of the 574-dimensional T3 surface space; trained on the
level-6/7 ground pairs it predicts the level-5 edge to 0.019 at 10 % of the boundary dimension (closure5).  V-E left open how to
build that state WITHOUT the deeper levels.

Construction tested here (no level >= 5 eigenvector is used).  By the Phase VII local-rules theorem, the neighbourhood of a
level-3 supertile in any hull tiling is one of the 72 legal 1-star types tau (the level-3 supertiling is again a hull tiling).
For each tau: the patch sigma^3(tau) (every tile of tau inflated three times), its pinned operator 24 - A_U, its K_ENV lowest
Kramers pairs; the restrictions of these eigenvectors to the surface of the central level-3 copy (canonical T3 tile order:
the central copy's descendants are generated in the same order as T3, and links depend only on relative frames, so the copy's
operator is literally T3's) are the snapshots.  U_env = leading left singular vectors of all 72 * 2 K_ENV snapshots.

Tests.  (1) capture of the T3-copy snapshots of the stored deep edge states (levels 5, 6, 7) by U_env vs V-E's level-6/7
snapshot subspace; (2) the compressed edge E_W of the level-5 supertile on its depth-2 partition (64 T3 copies) and of the
level-4 supertile (8 copies) with U_env as the per-copy basis (Rayleigh-Ritz upper bounds, Theorem E3), vs the exact edges.
Usage: python -u -I audit/phase8_env_fiber.py [K_ENV] -> audit/results/phase8_env_fiber.json"""
import os, sys, json, time, itertools
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); RES = os.path.join(HERE, 'results')
import numpy as np, scipy.sparse as sps, scipy.sparse.linalg as sla
import phase5e_rg as rg                               # installs the Windows `resource` stub before phase5d_schur
import phase5d_schur as d
import phase5e_run as run
import phase7_local as P
import phase7_adversarial as A
from phase7b_local_rules import legal_V1
from independent_clifford_q8_audit import FR30
T0 = time.time()
def log(*a): print(f"[{time.time()-T0:7.0f}s]", *a, flush=True)
MAT = np.array(A.MAT)

def patch_operator(poses):
    """pinned 24 - A_U on a list of poses (frames in Gs), via the cube-owner grid; returns csr (2n x 2n)."""
    G = np.array([g for g, t in poses], np.int64); T = np.array([t for g, t in poses], np.int64); n = len(G)
    cubes = P.cubes_of_poses(G, T); lo = cubes.reshape(-1, 3).min(0); shp = cubes.reshape(-1, 3).max(0) - lo + 2
    grid = np.full(tuple(shp), -1, np.int64); cc = cubes.reshape(-1, 3) - lo; grid[cc[:, 0], cc[:, 1], cc[:, 2]] = np.repeat(np.arange(n), 7)
    fi = P.frame_index(G); rows, cols, vals = [], [], []
    for ax in range(3):
        sa = [slice(None)] * 3; sb = [slice(None)] * 3; sa[ax] = slice(0, shp[ax] - 1); sb[ax] = slice(1, shp[ax])
        a, b = grid[tuple(sa)].ravel(), grid[tuple(sb)].ravel(); m = (a >= 0) & (b >= 0) & (a != b); a, b = a[m], b[m]
        C = P.LINKGI[fi[a], fi[b], ax]; C = C[..., 0] + 1j * C[..., 1]                  # (m, 2, 2) link a -> b
        for i in range(2):
            for j in range(2):
                v = C[:, i, j]; nz = np.abs(v) > 0.5
                rows += [2 * a[nz] + i, 2 * b[nz] + j]; cols += [2 * b[nz] + j, 2 * a[nz] + i]; vals += [-v[nz], -np.conj(v[nz])]
    d_ = np.arange(2 * n); rows.append(d_); cols.append(d_); vals.append(np.full(2 * n, 24.0 + 0j))
    H = sps.csr_matrix((np.concatenate(vals), (np.concatenate(rows), np.concatenate(cols))), shape=(2 * n, 2 * n))
    assert abs(H - H.conj().T).max() < 1e-12
    return H

def env_snapshots(V1, k_env, k=3):
    tiles = d.tiles_of(FR30, k); _, edges = d.build(tiles); deg = d.degrees(len(tiles), edges); surf_k = np.nonzero(deg < 24)[0]
    loc = d.spinor(surf_k); cols, meta = [], []
    for j, tau in enumerate(sorted(V1, key=lambda z: sorted(z))):
        poses, c = P.poses_from_key(tau)
        for _ in range(k): poses = P.inflate(poses)
        H = patch_operator(poses); n = H.shape[0] // 2
        w, V = sla.eigsh(H, k=2 * k_env, which='SA', tol=1e-10, ncv=max(40, 4 * k_env))
        o = np.argsort(w); w, V = w[o], V[:, o]
        base = 2 * (c * 8 ** k)                                        # spinor offset of the central copy
        X = V[base + loc, :]                                           # restriction to the central copy's surface
        cols.append(X); meta.append({'type': j, 'patch_tiles': n, 'E_low': float(w[0]), 'E_high': float(w[-1]), 'surface_weight_lowest': float(np.linalg.norm(X[:, 0]) ** 2)})
        if j % 12 == 0: log(f"  env {j}: patch {n} tiles, lowest {w[0]:.5f}, window [{w[0]:.4f}, {w[-1]:.4f}], central-surface weight of lowest {meta[-1]['surface_weight_lowest']:.3f}")
    return np.hstack(cols), meta, surf_k

def capture(U, X): return float(np.linalg.norm(U.conj().T @ X) ** 2 / np.linalg.norm(X) ** 2)

if __name__ == '__main__':
    k_env = int(sys.argv[1]) if len(sys.argv) > 1 else 8
    V1, _ = legal_V1(); log(f"|V_1| = {len(V1)}; building 72 environment patches sigma^3(tau), {k_env} Kramers pairs each")
    Xenv, meta, surf_k = env_snapshots(V1, k_env)
    Uenv, sv, _ = np.linalg.svd(Xenv, full_matrices=False); e = np.cumsum(sv ** 2) / (sv ** 2).sum()
    out = {'k_env': k_env, 'snapshots': int(Xenv.shape[1]), 'copy_surface_dim': int(Xenv.shape[0]), 'env_meta': meta,
           'env_d_for': {str(f): int(np.searchsorted(e, f) + 1) for f in (0.9, 0.99, 0.999)}}
    log(f"environment snapshots: {Xenv.shape[1]} columns; d for 90/99/99.9 % of their own weight: {out['env_d_for']}")
    # deep-level snapshots (stored V-E vectors) and V-E's deep-trained subspace
    vecs = run.fr30_vectors(); Xs = {}
    for L, v in vecs.items():
        v = np.asarray(v, complex); v = v / np.linalg.norm(v); Y = run.snapshots(v, L, 3, surf_k); Xs[L] = Y / np.linalg.norm(Y)
    U67, _, _ = np.linalg.svd(np.hstack([Xs[6], Xs[7]]), full_matrices=False)
    out['capture'] = {}
    for L in sorted(Xs):
        row = {'env': {str(dd): capture(Uenv[:, :dd], Xs[L]) for dd in (16, 34, 42, 58, 114, 200)},
               'deep67': {str(dd): capture(U67[:, :dd], Xs[L]) for dd in (16, 34, 42, 58, 114, 200)}}
        out['capture'][L] = row; log(f"capture of level-{L} T3-copy snapshots: env {row['env']}  | deep(6,7) {row['deep67']}")
    # principal angles between the env and deep subspaces at d = 58
    s_ = np.linalg.svd(Uenv[:, :58].conj().T @ U67[:, :58], compute_uv=False); out['cos_principal_d58'] = [float(x) for x in s_]
    log(f"principal cosines env vs deep(6,7) at d=58: min {s_.min():.3f}, median {np.median(s_):.3f}")
    # edge predictions
    E5 = json.load(open(os.path.join(RES, 'phase5e_level7_L5.json')))['eigenvalues'][0]
    s5 = rg.System(FR30, 5, depth=2); out['level5'] = {'E0': E5, 'rows': []}
    for dd in (34, 42, 58, 114):
        for name, U in (('env', Uenv), ('deep67', U67)):
            t0 = time.time(); red = rg.Reduced(s5, [U[:, :dd].copy() for _ in range(s5.nc)]); E, _ = red.root()
            row = {'basis': name, 'd': dd, 'D': red.D, 'D_frac': red.D / s5.offs[-1], 'E_W': E, 'err': E - E5}
            out['level5']['rows'].append(row); log(f"level-5 edge, {name} d={dd}: D={red.D} ({row['D_frac']:.3f})  E_W - E5 = {E - E5:+.5f} ({time.time()-t0:.0f}s)")
    s4 = rg.System(FR30, 4); E4 = rg.ground_state(s4)[0][0]; out['level4'] = {'E0': float(E4), 'rows': []}
    for dd in (34, 58, 114, 200):
        for name, U in (('env', Uenv), ('deep67', U67)):
            red = rg.Reduced(s4, [U[:, :dd].copy() for _ in range(8)]); E, _ = red.root()
            out['level4']['rows'].append({'basis': name, 'd': dd, 'D': red.D, 'err': E - E4}); log(f"level-4 edge, {name} d={dd}: E_W - E4 = {E - E4:+.5f}")
    json.dump(out, open(os.path.join(RES, 'phase8_env_fiber.json'), 'w'), indent=1)
    log('done')
