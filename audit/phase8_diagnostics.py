#!/usr/bin/env python3
"""Phase VIII diagnostics (deliverables/PHASE8_REPORT.md sections 4-7).  Each subcommand writes audit/results/phase8_<cmd>.json.

  geo        edge-state structure of the stored converged FR30 states (levels 5, 6, 7): weight vs graph distance to the depth-1
             seams, weight near the three mid-planes, depth-1 child weights, radius of gyration                       (sec. 5.1)
  fiber      fiber dimension of the edge-state restrictions to copies of T_k (k = 1..4), within level and across levels (sec. 4)
  seamctl    seam binding of the level-5 ground state for FR30, other rules, Abelian shadows, Z2, trivial, V-B controls (sec. 6a)
  slab       level-5 slab compressions around the mid-planes (transverse tail of the edge state)                       (sec. 5.1)
  chainloc   location / radius of gyration of the lowest state of sigma^m(tau) for the selecting types, m = 2, 3        (sec. 5.3)
  classpair  rules with identical level-4 plaquette class counts and different spectra (census search + levels 3-5)  (sec. 7)
  legality   fraction of tiles with an illegal 1-star in the V-B controls at level 5                                     (sec. 6b)
  dos        near-edge counting function of the pinned supertiles at levels 3-5                                          (sec. 5.1)
  poles      first pole lambda_II(k) of the surface response R_k(E) against the edge E_k, k = 1..5                        (sec. 5.2)
Usage: python -u -I audit/phase8_diagnostics.py <cmd> [<cmd> ...]"""
import os, sys, json, time, types, collections
sys.modules.setdefault('resource', types.SimpleNamespace(getrusage=lambda *a: types.SimpleNamespace(ru_maxrss=0), RUSAGE_SELF=0))
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); RES = os.path.join(HERE, 'results')
import numpy as np, scipy.sparse as sps, scipy.sparse.linalg as sla
T0 = time.time()
def log(*a): print(f"[{time.time()-T0:7.0f}s]", *a, flush=True)
def save(name, obj): json.dump(obj, open(os.path.join(RES, f'phase8_{name}.json'), 'w'), indent=1, default=float)

def seam_distance(n, a, b, L, depth=1):
    anc = np.arange(n) // 8 ** (L - depth); cross = anc[a] != anc[b]; seam = np.zeros(n, bool); seam[a[cross]] = True; seam[b[cross]] = True
    A = sps.csr_matrix((np.ones(len(a)), (a, b)), shape=(n, n)); A = ((A + A.T) > 0).astype(np.int8)
    dist = np.full(n, -1); fr = np.nonzero(seam)[0]; dist[fr] = 0; k = 0
    while len(fr):
        k += 1; nb = A[fr].indices; nb = np.unique(nb[dist[nb] < 0]); dist[nb] = k; fr = nb
    return seam, dist

def fr30_geometry(L):
    import phase7_local as P
    from phase7b_controls import geometry, panels
    from independent_clifford_q8_audit import FR30
    G, T, grid, _ = geometry(FR30, L); pan = panels(grid)
    a = np.concatenate([p[0] for p in pan]); b = np.concatenate([p[1] for p in pan]); X = P.cubes_of_poses(G, T).mean(1) + 0.5
    return G, T, X, a, b

def cmd_geo():
    files = {5: ('phase5e_fr30_level7_L5_lowest4.npy', [(0, 2, 'pair1'), (2, 4, 'pair2')]), 6: ('phase5b_e_fr30_level6_groundstate.npy', [(0, 1, 'vec1')]),
             7: ('phase5e_fr30_level7_lowest4.npy', [(0, 2, 'pair1'), (2, 4, 'pair2')])}
    out = {}
    for L, (f, groups) in files.items():
        G, T, X, a, b = fr30_geometry(L); n = len(G); mid = 2 ** L; seam, dist = seam_distance(n, a, b, L)
        V = np.load(os.path.join(RES, f), mmap_mode='r'); V = np.asarray(V).reshape(V.shape[0], -1)
        for s_, e_, lab in groups:
            v = np.asarray(V[:, s_:e_]); w = (np.abs(v[0::2]) ** 2 + np.abs(v[1::2]) ** 2).sum(1); w /= w.sum()
            com = (w[:, None] * X).sum(0); rg = float(np.sqrt((w * ((X - com) ** 2).sum(1)).sum()))
            out[f'L{L}_{lab}'] = {'seam_weight_by_distance': [float(w[dist == k].sum()) for k in range(8)], 'seam_tile_fraction': float(seam.mean()),
                                  'midplane_weight_within2': [float(w[np.abs(X[:, i] - mid) < 2.0].sum()) for i in range(3)],
                                  'child_weights': np.bincount(np.arange(n) // 8 ** (L - 1), weights=w, minlength=8).tolist(),
                                  'centre_of_mass': com.tolist(), 'radius_of_gyration': rg, 'rg_over_box': rg / 2 ** (L + 1)}
            log(f"geo L{L} {lab}: seam weight by distance {np.round(out[f'L{L}_{lab}']['seam_weight_by_distance'][:4], 3).tolist()}, Rg/box {rg / 2 ** (L + 1):.3f}")
    save('geo', out)

def cmd_fiber():
    import phase5e_rg as rg, phase5d_schur as d, phase5e_run as run
    from independent_clifford_q8_audit import FR30
    vecs = run.fr30_vectors(); out = {}
    def cap(U, X): return float(np.linalg.norm(U.conj().T @ X) ** 2 / np.linalg.norm(X) ** 2)
    for k in (1, 2, 3, 4):
        tiles = d.tiles_of(FR30, k); _, edges = d.build(tiles); deg = d.degrees(len(tiles), edges); surf = np.nonzero(deg < 24)[0]; Xs = {}; row = {'copy_surface_dims': int(2 * len(surf)), 'within': {}, 'transfer': {}}
        for L in sorted(vecs):
            if L - k < 1: continue
            v = np.asarray(vecs[L], complex); v = v / np.linalg.norm(v); X = run.snapshots(v, L, k, surf); Xs[L] = X / np.linalg.norm(X)
            sv = np.linalg.svd(Xs[L], compute_uv=False); e = np.cumsum(sv ** 2) / (sv ** 2).sum()
            row['within'][L] = {'copies': int(8 ** (L - k)), 'surface_weight': float(np.linalg.norm(X) ** 2 / 2), 'd': [int(np.searchsorted(e, f) + 1) for f in (0.9, 0.99, 0.999)]}
        Ls = sorted(Xs)
        for i, tr in enumerate(Ls[:-1]):
            U, _, _ = np.linalg.svd(Xs[tr], full_matrices=False)
            for te in Ls[i + 1:]: row['transfer'][f'{tr}->{te}'] = {str(dd): cap(U[:, :dd], Xs[te]) for dd in (16, 32, 64)}
        sv = np.linalg.svd(np.hstack([Xs[L] for L in Ls]), compute_uv=False); e = np.cumsum(sv ** 2) / (sv ** 2).sum()
        row['union_d'] = [int(np.searchsorted(e, f) + 1) for f in (0.9, 0.99, 0.999)]; out[k] = row; log(f"fiber k={k}: within {row['within']}; union {row['union_d']}")
    save('fiber', out)

def cmd_seamctl(L=5):
    from independent_clifford_q8_audit import FR30, panel_edges
    from phase5a_controls import clifford_links, build_H
    from phase5b_controls import system_tiles
    from phase7b_controls import geometry, panels, link_field
    from phase7b_scaling import scalar_operator
    from phase7_abelian_check import REFLECTION_ONLY
    out = {}
    for name in ['fr30', 'dec1387', 'dec3697', 'dec2238', 'iid1', 'coarse1', 'fine1', 'shuffle1', 'flip1,0.05', 'trivial', 'Z2_reflect', 'FR30_chi1', 'FR30_chi2']:
        if name in ('trivial', 'Z2_reflect', 'FR30_chi1', 'FR30_chi2'):
            dec = REFLECTION_ONLY if name == 'Z2_reflect' else FR30; G, T, grid, fid = geometry(dec, L); n = len(G); pan = panels(grid)
            Hs = scalar_operator(n, pan, link_field(fid, pan, 'trivial' if name == 'trivial' else 'clifford'), {'FR30_chi1': 1, 'FR30_chi2': 2}.get(name)).astype(float)
            ev, V = sla.eigsh(Hs, k=2, which='SA', tol=1e-10, ncv=40); i = int(np.argmin(ev)); w = V[:, i] ** 2
            a = np.concatenate([p[0] for p in pan]); b = np.concatenate([p[1] for p in pan]); E0 = float(ev[i])
        else:
            tiles, _ = system_tiles(name, L); n = len(tiles); _, ed = panel_edges(tiles); H = build_H(n, ed, clifford_links(tiles, ed), np.full(n, 24.0)).tocsr()
            ev, V = sla.eigsh(H, k=2, which='SA', tol=1e-10, ncv=40); i = int(np.argmin(ev)); v = V[:, i]; w = np.abs(v[0::2]) ** 2 + np.abs(v[1::2]) ** 2
            a = np.array([e[0] for e in ed]); b = np.array([e[1] for e in ed]); E0 = float(ev[i])
        w = w / w.sum(); seam, dist = seam_distance(n, a, b, L)
        out[name] = {'E0': E0, 'seam_weight_by_distance': [float(w[dist == k].sum()) for k in range(4)], 'seam_tile_fraction': float(seam.mean()),
                     'enrichment': float(w[dist == 0].sum() / seam.mean()), 'ipr_n': float((w ** 2).sum() * n)}
        log(f"seamctl L{L} {name}: E0 {E0:.6f}, seam weight {out[name]['seam_weight_by_distance'][0]:.3f} (enrichment {out[name]['enrichment']:.2f}), IPR*n {out[name]['ipr_n']:.1f}")
    save('seamctl', out)

def cmd_slab(L=5):
    import phase7_local as P
    from phase7b_controls import geometry, panels, link_field
    from phase7b_scaling import operator_fast
    from independent_clifford_q8_audit import FR30
    G, T, grid, fid = geometry(FR30, L); n = len(G); pan = panels(grid)
    Re, Im = operator_fast(n, pan, link_field(fid, pan, 'clifford')); H = (Re + 1j * Im).tocsr().astype(complex); X = P.cubes_of_poses(G, T).mean(1) + 0.5; mid = 2 ** L
    def bottom(sel):
        idx = np.nonzero(sel)[0]; sp = np.ravel(np.c_[2 * idx, 2 * idx + 1]); return float(sla.eigsh(H[sp][:, sp], k=2, which='SA', tol=1e-10, ncv=48, return_eigenvectors=False).min()), len(idx)
    full = bottom(np.ones(n, bool))[0]; out = {'full': full, 'rows': []}
    for w in (2, 3, 4, 6, 8, 12):
        for name, sel in (('plane_x', np.abs(X[:, 0] - mid) < w), ('three_planes', (np.abs(X - mid) < w).any(1))):
            e, m = bottom(sel); out['rows'].append({'half_width': w, 'slab': name, 'bottom': e, 'excess': e - full, 'tiles': m}); log(f"slab w={w} {name}: +{e - full:.4f}")
    save('slab', out)

def cmd_chainloc():
    import phase7_local as P
    from phase8_env_fiber import patch_operator
    from phase8_patch_bounds import types_sorted
    Ts = types_sorted(); out = {}
    for j in (59, 63, 35, 39, 26):
        tau = Ts[j]; poses0, c = P.poses_from_key(tau); out[j] = {}
        for m in (2, 3):
            poses = poses0
            for _ in range(m): poses = P.inflate(poses)
            H = patch_operator(poses); w, V = sla.eigsh(H, k=2, which='SA', tol=1e-11, ncv=48); v = V[:, np.argmin(w)]
            wt = np.abs(v[0::2]) ** 2 + np.abs(v[1::2]) ** 2; wt /= wt.sum()
            G = np.array([g for g, t in poses]); Tt = np.array([t for g, t in poses]); X = P.cubes_of_poses(G, Tt).mean(1) + 0.5
            per = np.bincount(np.arange(len(poses)) // 8 ** m, weights=wt, minlength=len(tau)); com = (wt[:, None] * X).sum(0)
            out[j][m] = {'E': float(w.min()), 'central_weight': float(per[c]), 'top_parent_weights': np.sort(per)[::-1][:3].tolist(), 'centre_of_mass': com.tolist(),
                         'radius_of_gyration': float(np.sqrt((wt * ((X - com) ** 2).sum(1)).sum())), 'central_supertile_side': 2 ** (m + 1)}
            log(f"chainloc type {j} m={m}: E {w.min():.6f}, com {np.round(com, 1).tolist()}, Rg {out[j][m]['radius_of_gyration']:.1f}")
    save('chainloc', out)

def cmd_classpair():
    from independent_clifford_q8_audit import panel_edges
    from phase5a_controls import clifford_links, build_H
    from phase5b_controls import system_tiles
    D = json.load(open(os.path.join(RES, 'phase5b_sweep.json'))); R = D['records']; groups = collections.defaultdict(list)
    for r in R:
        p = r['pred']; groups[(p['n_plus'], p['n_minus'], tuple(sorted((p['n_i'], p['n_j'], p['n_k']))))].append(r)
    multi = [(k, rs) for k, rs in groups.items() if len({round(r['L3']['lambda'][0], 7) for r in rs}) > 1]
    out = {'census_rules': len(R), 'class_count_groups': len(groups), 'groups_with_distinct_bottoms': len(multi), 'groups': []}
    for key, rs in multi:
        rows = []
        for r in rs:
            row = {'index': r['index'], 'Y3': r['L3']['lambda'][0]}
            for L in (4, 5):
                tiles, _ = system_tiles(f"dec{r['index']}", L); n = len(tiles); _, ed = panel_edges(tiles)
                H = build_H(n, ed, clifford_links(tiles, ed), np.full(n, 24.0)).tocsr(); row[f'Y{L}'] = float(sla.eigsh(H, k=2, which='SA', tol=1e-10, return_eigenvectors=False).min())
            row['pred'] = {k: v for k, v in r['pred'].items() if isinstance(v, (int, float))}; rows.append(row); log(f"classpair rule {r['index']}: Y3 {row['Y3']:.6f} Y4 {row['Y4']:.6f} Y5 {row['Y5']:.6f}")
        g = collections.defaultdict(list)
        for row in rows: g[round(row['Y3'], 6)].append(row)
        A_, B_ = list(g.values())[:2]; same = [k for k in A_[0]['pred'] if {round(x['pred'][k], 9) for x in A_} == {round(x['pred'][k], 9) for x in B_}]
        out['groups'].append({'class_counts': [key[0], key[1], *key[2]], 'rules': [{k: v for k, v in r.items() if k != 'pred'} for r in rows],
                              'identical_statistics': same, 'different_statistics': [k for k in A_[0]['pred'] if k not in same]})
    save('classpair', out)

def cmd_legality(L=5):
    import phase7_local as P
    from phase7b_local_rules import legal_V1
    from phase5b_controls import system_tiles
    V1, _ = legal_V1(); out = {}
    for name in ('fr30', 'iid1', 'coarse1', 'fine1', 'shuffle1', 'flip1,0.05', 'flip1,0.2'):
        tiles, _ = system_tiles(name, L); G = np.array([t[0] for t in tiles], np.int64); T = np.array([t[1] for t in tiles], np.int64)
        grid = P.owner_grid(L, G, T); cnt, ncomp = P.star_types(G, T, grid, P.LODD[1]); illegal = sum(v for k, v in cnt.items() if k not in V1)
        out[name] = {'complete_1stars': int(ncomp), 'illegal': int(illegal), 'illegal_fraction': illegal / ncomp, 'distinct_types': len(cnt)}; log(f"legality {name}: {out[name]}")
    save('legality', out)

def fr30_H(L):
    from independent_clifford_q8_audit import FR30, panel_edges
    from phase5a_controls import clifford_links, build_H
    from phase5b_controls import system_tiles
    tiles, _ = system_tiles('fr30', L); n = len(tiles); _, ed = panel_edges(tiles)
    return build_H(n, ed, clifford_links(tiles, ed), np.full(n, 24.0)).tocsr(), n, ed

def low_spectrum(H, emax, sigma):
    """all eigenvalues of H below emax (dense for small H, shift-invert Lanczos otherwise, k doubled until emax is passed)"""
    if H.shape[0] <= 9000: w = np.linalg.eigvalsh(H.toarray()); return w[w <= emax]
    k = 200
    while True:
        w = np.sort(sla.eigsh(H, k=k, sigma=sigma, which='LM', tol=1e-10, return_eigenvectors=False))
        if w[-1] > emax: return w[w <= emax]
        k *= 2

def cmd_dos():
    """near-edge counting function of the pinned supertiles: N_L(delta) = #{eigenvalues <= E_L + delta} (Kramers pairs count 2).
    A 2D seam band predicts N ~ 4^L delta; a 3D bulk band predicts N ~ 8^L delta^(3/2)."""
    deltas = [0.005, 0.01, 0.02, 0.05, 0.1, 0.2]; out = {'deltas': deltas, 'levels': {}}
    for L in (3, 4, 5):
        H, n, _ = fr30_H(L); E0 = float(sla.eigsh(H, k=2, which='SA', tol=1e-12, return_eigenvectors=False).min())
        w = low_spectrum(H, E0 + max(deltas) + 1e-9, E0 - 0.01)
        out['levels'][L] = {'tiles': n, 'E_L': E0, 'count': [int((w <= E0 + dl + 1e-12).sum()) for dl in deltas], 'eigenvalues': w.tolist()}
        log(f"dos L{L}: E_L {E0:.6f}, counts {out['levels'][L]['count']}")
    for L in (4, 5):
        out['levels'][L]['ratio_to_previous'] = [a / b if b else None for a, b in zip(out['levels'][L]['count'], out['levels'][L - 1]['count'])]
    save('dos', out)

def cmd_poles():
    """the first pole of the surface response R_k(E): lambda_II(k) = lambda_min of the interior block of H(T_k), against E_k"""
    import phase5d_schur as d
    from independent_clifford_q8_audit import FR30
    out = {}
    for k in (1, 2, 3, 4, 5):
        tiles = d.tiles_of(FR30, k); H, edges = d.build(tiles); n = len(tiles); deg = d.degrees(n, edges); H = H.tocsr()
        I = np.nonzero(deg == 24)[0]; ii = d.spinor(I)
        def lo(M): return float(np.linalg.eigvalsh(M.toarray())[0]) if M.shape[0] <= 9000 else float(sla.eigsh(M, k=2, which='SA', tol=1e-12, return_eigenvectors=False).min())
        out[k] = {'tiles': n, 'interior_tiles': int(len(I)), 'E_k': lo(H), 'lambda_II': lo(H[ii][:, ii]) if len(I) else None}
        log(f"poles k={k}: {out[k]}")
    save('poles', out)

if __name__ == '__main__':
    for c in sys.argv[1:]: globals()[f'cmd_{c}']()
