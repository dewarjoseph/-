#!/usr/bin/env python3
"""Phase VII-B (D): second, independent implementation and small-case tests of the localization theorem (phase7_ims.py).

Independent of phase7_ims.py: tiles from independent_clifford_q8_audit.tiles_at_level, operators from phase5a_controls
(clifford_links/build_H), ball keys from raw relative poses (no phase7_local.encode), overlap c(|h|/rho) by numerical radial
quadrature (no closed form).  Shared with phase7_ims.py: the definitions (centroids, balls |x_a - x_t| < R, rho = R - 311/175)
and the FR30 decoration.

1. overlap: int phi(z) phi(z+h) dz / ||phi||^2 by a CARTESIAN grid quadrature in R^3 vs the closed form c(eta).
2. census of FR30 ball patches in the interior of the level-6 supertile (R = 6, 8): number of distinct balls, D_R = min
   lambda_min((24 - A)|ball), Lambda_R = min lambda_min((24 - A~)|ball) -- compared with phase7_ims.json.
3. finite-patch tests of the inequality direction: for a level-3 supertile K inside the level-5 supertile, and trivial / Z2 /
   FR30 links, lambda_min((24 - A)|K) >= min over tiles t near K of lambda_min((24 - A~)|(B_t cap K)) must hold.
4. localization constant: K(rho0) = sup over 0 < eta <= (15/7)/rho0 of (1/c(eta) - 1)/eta^2 (interval arithmetic), so that
   eps(rho) <= K(rho0) S_1 / rho^2 for rho >= rho0.
Usage: python -u -I audit/phase7b_ims_check.py -> audit/results/phase7b_ims_check.json"""
import os, sys, json, time, math, itertools, collections
from fractions import Fraction
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); RES = os.path.join(HERE, 'results')
import numpy as np, scipy.sparse as sps
from scipy.integrate import quad
from scipy.spatial import cKDTree
from independent_clifford_q8_audit import FR30, tiles_at_level, panel_edges, clifford_link
from phase5a_controls import clifford_links, build_H
T0 = time.time()
def log(*a): print(f"[{time.time()-T0:7.0f}s]", *a, flush=True)
RC = 311 / 175

def c_numeric(h, rho):
    """radial convolution formula evaluated by adaptive quadrature (not the closed form)"""
    F = lambda r: math.sin(math.pi * r / rho) if 0 <= r <= rho else 0.0
    inner = lambda r: quad(F, abs(h - r), min(h + r, rho), epsabs=1e-13)[0]
    return 2 * math.pi / h * quad(lambda r: F(r) * inner(r), 0, rho, limit=200, epsabs=1e-13)[0] / (2 * math.pi * rho)

def c_closed(eta): return (math.pi * (1 - eta / 2) * math.sin(math.pi * eta) + 1 - math.cos(math.pi * eta)) / (math.pi ** 2 * eta)

def overlap_cartesian(hvec, rho, n=161):
    g = np.linspace(-rho - 3, rho + 3, n); dx = g[1] - g[0]; X, Y, Z = np.meshgrid(g, g, g, indexing='ij')
    def phi(x, y, z):
        r = np.sqrt(x * x + y * y + z * z); out = np.where(r < rho, np.sinc(r / rho) * math.pi / rho, 0.0)   # sin(pi r/rho)/r
        return out
    a = phi(X, Y, Z); b = phi(X + hvec[0], Y + hvec[1], Z + hvec[2])
    return float((a * b).sum() / (a * a).sum())

def centroids(tiles): return np.array([np.mean(np.array(sorted(cs)), 0) + 0.5 for _, _, cs in tiles])
def centroid14(tiles): return np.array([2 * np.array(sorted(cs)).sum(0) + 7 for _, _, cs in tiles], np.int64)   # 14 x, exact

def ball_operator(sub, rho, cfun):
    """(24 - A) and (24 - A~) on the tile list sub (pinned diagonal 24), A~_ab = A_ab / c(|x_a - x_b|/rho)"""
    _, ed = panel_edges(sub); links = clifford_links(sub, ed); n = len(sub)
    H = build_H(n, ed, links, np.full(n, 24.0)).toarray(); X = centroids(sub); Ht = H.copy(); cache = {}
    for a in range(n):
        for b in range(n):
            if a != b and np.abs(H[2*a:2*a+2, 2*b:2*b+2]).max() > 0:
                h = round(float(np.linalg.norm(X[a] - X[b])), 12)
                if h not in cache: cache[h] = cfun(h, rho)
                Ht[2*a:2*a+2, 2*b:2*b+2] = H[2*a:2*a+2, 2*b:2*b+2] / cache[h]
    return H, Ht

def census(R, level=6):
    rho = R - RC; tl = tiles_at_level(FR30, level); n = len(tl); X = centroids(tl); N = 2 ** (level + 1)
    occupied = np.zeros((N, N, N), bool)
    for _, _, cs in tl:
        for c in cs: occupied[c] = True
    # interior: the Chebyshev (R+2)-neighbourhood of the tile's cubes is occupied (so its ball is the infinite-tiling ball)
    pad = R + 2; tree = cKDTree(X); X14 = centroid14(tl); balls = {}; t0 = time.time()
    for t in range(n):
        cs = np.array(sorted(tl[t][2])); lo = cs.min(0) - pad; hi = cs.max(0) + pad
        if (lo < 0).any() or (hi >= N).any() or not occupied[lo[0]:hi[0]+1, lo[1]:hi[1]+1, lo[2]:hi[2]+1].all(): continue
        mem = [m for m in tree.query_ball_point(X[t], R + 1e-6) if int(((X14[m] - X14[t]) ** 2).sum()) < 196 * R * R]   # exact
        Gt, Tt, _ = tl[t]
        key = tuple(sorted((tuple((Gt.T @ tl[m][0]).ravel()), tuple(Gt.T @ (tl[m][1] - Tt))) for m in mem))
        if key not in balls: balls[key] = mem
    log(f"census R={R}: {len(balls)} distinct ball patches in the interior of T_{level} ({time.time()-t0:.0f}s)")
    D = []; Lt = []
    for key, mem in balls.items():
        H, Ht = ball_operator([tl[m] for m in mem], rho, c_numeric)
        D.append(np.linalg.eigvalsh(H)[0]); Lt.append(np.linalg.eigvalsh(Ht)[0])
    return {'R': R, 'distinct_balls': len(balls), 'D_R_float': float(min(D)), 'Lambda_R_float': float(min(Lt)), 'seconds': time.time() - t0}

def finite_patch_test(R=6, level=5):
    """K = a level-3 supertile deep inside T_level; lambda_min(H|K) vs the IMS lower bound restricted to K"""
    import phase7_local as P
    from phase7_abelian_check import REFLECTION_ONLY
    from phase7b_controls import SIGNED, SKEY, LQ, CHI
    import phase7_adversarial as A
    rho = R - RC; out = {}
    for name, dec, kind in (('FR30', FR30, 'clifford'), ('Z2_reflect', REFLECTION_ONLY, 'clifford'), ('trivial', FR30, 'trivial')):
        ops = P.make_ops(dec); P.GOPS = np.array([g for g, t in ops]); P.TOPS = np.array([t for g, t in ops])
        G, T = P.gen_poses(level); n = len(G); C = P.cubes_of_poses(G, T); X = C.mean(1) + 0.5; X14 = 2 * C.sum(1) + 7
        fid = np.array([SKEY[tuple(np.asarray(g, int).ravel())] for g in G]); grid = P.owner_grid(level, G, T); Nb = grid.shape[0]
        # dense operator pieces on demand: panel list
        pan = []
        for ax in range(3):
            sa = [slice(None)] * 3; sb = [slice(None)] * 3; sa[ax] = slice(0, Nb - 1); sb[ax] = slice(1, Nb)
            a, b = grid[tuple(sa)], grid[tuple(sb)]; m = (a >= 0) & (b >= 0) & (a != b)
            for x, y in zip(a[m], b[m]): pan.append((int(x), int(y), ax))
        def link(a, b, ax): return np.eye(2) if kind == 'trivial' else np.array(A.MAT[LQ[fid[a], fid[b], ax]])
        nbr = collections.defaultdict(list)
        for a, b, ax in pan: nbr[a].append((b, link(a, b, ax))); nbr[b].append((a, link(a, b, ax).conj().T))
        def op(S, amp):
            idx = {t: i for i, t in enumerate(S)}; Hm = np.eye(2 * len(S), dtype=complex) * 24
            for t in S:
                for u, U in nbr[t]:
                    if u in idx:
                        f = 1 / c_closed(np.linalg.norm(X[t] - X[u]) / rho) if amp else 1.0
                        Hm[2*idx[t]:2*idx[t]+2, 2*idx[u]:2*idx[u]+2] -= f * U
            return Hm
        # choose the level-3 supertile whose centroid is closest to the centre of T_level's bounding box
        anc = np.arange(n) // 8 ** 3; cen = np.array([X[anc == j].mean(0) for j in range(n // 512)])
        j0 = int(np.argmin(np.linalg.norm(cen - Nb / 2, axis=1))); K = list(np.nonzero(anc == j0)[0]); Kset = set(K)
        lamK = float(np.linalg.eigvalsh(op(K, False))[0])
        tree = cKDTree(X); near = set()
        for t in K: near.update(tree.query_ball_point(X[t], rho + 2 * RC + 1e-9))
        # every tile t whose closure can contain a y with supp chi_y meeting K is within rho + r_c of a K centroid
        margin = min(min(np.min(np.abs(C[t] - 0)), np.min(np.abs(C[t] - (Nb - 1)))) for t in near)
        best = math.inf
        for t in near:
            S = [m for m in tree.query_ball_point(X[t], R + 1e-6) if m in Kset and int(((X14[m] - X14[t]) ** 2).sum()) < 196 * R * R]
            if S: best = min(best, float(np.linalg.eigvalsh(op(S, True))[0]))
        out[name] = {'lambda_min_K': lamK, 'ims_lower_bound_K': best, 'holds': best <= lamK + 1e-12, 'tiles_t_used': len(near), 'margin_cubes': int(margin)}
        log(f"finite patch {name}: lambda_min(H|K) = {lamK:.6f} >= IMS bound {best:.6f}: {best <= lamK + 1e-12}")
    return out

def k_constant(rho0):
    """analytic: 1 - c(eta) = (1/2) int (chi_y(a) - chi_y(b))^2 dy <= pi^2 eta^2 / 6 (Fourier: 4 sin^2(x/2) <= x^2, isotropy of phi),
    so 1/c - 1 <= (pi^2 eta^2/6) / (1 - pi^2 eta^2/6) <= K eta^2 for eta <= eta_max = (15/7)/rho0, K = (pi^2/6)/(1 - pi^2 eta_max^2/6).
    Checked here against the closed form on a fine grid."""
    pi2 = math.pi ** 2 * (1 + 1e-15); eta_max = (15 / 7) / rho0; K = (pi2 / 6) / (1 - pi2 * eta_max ** 2 / 6)
    grid = np.linspace(1e-4, eta_max, 20001); worst = max((1 / c_closed(e) - 1) / e ** 2 for e in grid)
    lower_ok = all(c_closed(e) >= 1 - math.pi ** 2 * e * e / 6 - 1e-15 for e in grid)
    return {'rho0': rho0, 'eta_max': eta_max, 'K_upper': K, 'max_on_grid': worst, 'c_ge_1_minus_pi2eta2over6_on_grid': lower_ok, 'pi2_over_6': math.pi ** 2 / 6}

if __name__ == '__main__':
    out = {}
    rows = []
    for rho in (4.2229, 6.2229, 10.2229):
        for hv in ((1, 1, 1), (2, 0, 0), (15 / 7, 0, 0), (1.2, 0.9, 1.0)):
            h = float(np.linalg.norm(hv)); cart = overlap_cartesian(np.array(hv, float), rho); rows.append({'rho': rho, 'h': h, 'cartesian': cart, 'radial_quad': c_numeric(h, rho), 'closed': c_closed(h / rho)})
    out['overlap'] = rows; dev = max(max(abs(r['cartesian'] - r['closed']), abs(r['radial_quad'] - r['closed'])) for r in rows)
    log(f"overlap: max |cartesian or radial quadrature - closed form| = {dev:.2e}")
    out['K'] = {str(r0): k_constant(r0) for r0 in (4.2229, 6.2229, 10.2229)}; log(f"K constants: {[round(v['K_upper'], 5) for v in out['K'].values()]}")
    json.dump(out, open(os.path.join(RES, 'phase7b_ims_check.json'), 'w'), indent=1)
    out['finite_patch'] = finite_patch_test(); json.dump(out, open(os.path.join(RES, 'phase7b_ims_check.json'), 'w'), indent=1)
    for R in (6, 8):
        out[f'census_R{R}'] = census(R); log(out[f'census_R{R}']); json.dump(out, open(os.path.join(RES, 'phase7b_ims_check.json'), 'w'), indent=1)
