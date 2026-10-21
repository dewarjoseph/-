#!/usr/bin/env python3
"""Phase V-B, Workstream B: complete census of admissible chair decorations and preregistered predictor analysis.

DECORATION SPACE.  A parity-admissible decoration assigns to the centre child one of the 3 even permutations and to each
of the 7 octant children v in U3 one of the 3 permutations of parity (-1)^{|v|} (even for |v| even, odd for |v| odd),
exactly the rule of audit/phase5a_controls.random_decoration.  There are 3^8 = 6561 decorations; FR30 is one of them.
Decoration index i in [0, 6561): base-3 digits (d0, d1..d7) with d0 the centre choice in EVEN and d_k the choice for
U3[k-1] in EVEN or ODD (lists as in phase5a_controls, i.e. itertools.permutations order filtered by sign).

PREREGISTERED PROTOCOL (fixed before any spectral result of this sweep was inspected; see docstring of `analyze`):
  Outcome  Y3 = lambda_min(24 I - A) of the level-3 pinned patch (dense, exact to 1e-13), for ALL 6561 decorations.
           Y4 = the same at level 4 (LOBPCG, residual <= 1e-7) for the preregistered sample S4 = {FR30} u 400 decorations
           drawn without replacement with numpy default_rng(20261022) from the 6560 non-FR30 indices (drawn BEFORE any
           spectral computation; the sample is saved).
  Flux baseline: OLS  Y ~ 1 + f_trl + f_m1  on level-4 class fractions of inter-tile plaquettes (the same fractions that
           the periodic census regression uses).  Out-of-sample performance by 10-fold cross-validation (fixed fold seed
           20261022), reported as CV-R^2 and CV-RMSE.
  Primary structural predictors (from Phase V-A, tested at alpha = 0.05/3): enr1_trl (depth-1 interface enrichment of
           traceless plaquettes), cv_m1 (coefficient of variation of the per-tile count of -1 plaquettes), pair_m1
           (nearest-neighbour clustering of -1 plaquettes).  Test = improvement of CV-R^2 over the flux baseline when the
           predictor is added, with a permutation test (predictor column permuted, 200 permutations) for the p-value.
  Exploratory predictors (Bonferroni over their number): depth-2/3 enrichments of -1 and traceless; CV of traceless and
           of nontrivial per-tile counts; class-pair correlation matrices for plaquettes sharing a panel and sharing a
           tile (6 entries each); loop-class fractions of 2x1 and 2x2 loops; hierarchical variance of -1 counts over the
           8 depth-1 and 64 depth-2 children; axis-resolved fractions f_i, f_j, f_k (Q8-gauge, not SU(2), invariant).
  Collinearity: report the correlation of each predictor with f_m1 and f_trl and the variance inflation factor; a
           predictor whose partial effect vanishes after conditioning on flux is reported as a flux proxy.
  Exact-flux-matched comparison: decorations with IDENTICAL level-4 class-count vectors (+1, -1, i, j, k) are grouped;
           within-group spread of Y3 is reported (this is a matched-flux comparison with zero flux tolerance).

Everything printed is computed in this run.  Usage (from the repository root):
   python3 -u -I audit/phase5b_sweep.py census <shard> <nshards>       # level-3 bottoms + level-4 flux/predictors
   python3 -u -I audit/phase5b_sweep.py level4 <shard> <nshards>       # level-4 bottoms for the preregistered sample
   python3 -u -I audit/phase5b_sweep.py merge                           # merge shards -> audit/results/phase5b_sweep.json
   python3 -u -I audit/phase5b_sweep.py analyze                         # preregistered analysis -> phase5b_sweep_analysis.txt
"""
import os, sys, time, json, itertools, resource
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
RES = os.path.join(HERE, 'results')
import numpy as np, scipy.linalg as sla
from independent_clifford_q8_audit import FR30, U3, tiles_at_level, panel_edges
from phase5a_controls import clifford_links, build_H, degrees, EVEN, ODD
from phase5a_scaling_controls import eig_lobpcg
import phase5a_flux_vs_edge as fe

SAMPLE_SEED = 20261022; SAMPLE_SIZE = 400; FOLD_SEED = 20261022; NPERM = 200
NDEC = 3 ** 8

# ---------------------------------------------------------------- decorations
def decoration(i):
    digits = []
    for _ in range(8): digits.append(i % 3); i //= 3
    dec = {'0': EVEN[digits[0]]}
    for k, v in enumerate(U3): dec[v] = (EVEN if sum(v) % 2 == 0 else ODD)[digits[k + 1]]
    return dec

def index_of(dec):
    digs = [EVEN.index(dec['0'])] + [(EVEN if sum(v) % 2 == 0 else ODD).index(dec[v]) for v in U3]
    return sum(d * 3 ** k for k, d in enumerate(digs))

FR30_INDEX = index_of(FR30)
assert decoration(FR30_INDEX) == FR30

def sample_indices():
    rng = np.random.default_rng(SAMPLE_SEED)
    pool = np.array([i for i in range(NDEC) if i != FR30_INDEX])
    return [FR30_INDEX] + sorted(rng.choice(pool, SAMPLE_SIZE, replace=False).tolist())

# ---------------------------------------------------------------- predictors
def anc(owners, L, d): return owners // 8 ** (L - d)

def class_pair_stats(owners, cl, n):
    """Joint class statistics for plaquette pairs sharing a tile.  Returns normalised 3x3 matrix C[a,b] =
    P(classes a,b | pair) / (P(a) P(b)) for the symmetrised pair distribution over unordered pairs sharing >= 1 tile."""
    m = len(cl); f = np.bincount(cl, minlength=3) / m
    # incidence tile -> plaquettes (distinct owners)
    o = np.sort(owners, axis=1); d = np.ones_like(o, bool); d[:, 1:] = o[:, 1:] != o[:, :-1]
    pl = np.repeat(np.arange(m), d.sum(axis=1)); ti = o[d]
    order = np.argsort(ti, kind='stable'); ti = ti[order]; pl = pl[order]
    counts = np.bincount(ti, minlength=n); starts = np.concatenate([[0], np.cumsum(counts)])
    J = np.zeros((3, 3))
    # per tile: all unordered pairs of its plaquettes; count class pairs (vectorised per tile size group)
    for size in np.unique(counts):
        if size < 2: continue
        tiles = np.nonzero(counts == size)[0]
        idx = np.stack([pl[starts[t]:starts[t] + size] for t in tiles])      # (ntiles, size)
        c = cl[idx]
        for a in range(size):
            for b in range(a + 1, size):
                np.add.at(J, (c[:, a], c[:, b]), 1)
    J = J + J.T; J /= J.sum()
    with np.errstate(divide='ignore', invalid='ignore'):
        C = J / np.outer(f, f)
    return C

def panel_pair_stats(owners_edges, cl, grid_edges, N):
    """Joint class statistics for plaquette pairs around the same unit panel (square).  The 4 edges of the square with
    corner p and axes a<b are (p,a), (p,b), (p+e_a,b), (p+e_b,a); every pair of these 4 plaquettes 'shares the panel'.
    Vectorised through an edge-index grid."""
    m = len(cl); f = np.bincount(cl, minlength=3) / m
    pts = grid_edges[:, :3]; axes = grid_edges[:, 3]
    EG = -np.ones((N + 1, N + 1, N + 1, 3), int); EG[pts[:, 0], pts[:, 1], pts[:, 2], axes] = np.arange(m)
    J = np.zeros((3, 3)); npairs = 0
    E3 = np.eye(3, dtype=int)
    for a in range(3):
        for b in range(a + 1, 3):
            sel = np.nonzero(axes == a)[0]; p = pts[sel]
            pa = p + E3[a]; pb = p + E3[b]
            ok = (pa.max(axis=1) <= N) & (pb.max(axis=1) <= N)
            p, pa, pb = p[ok], pa[ok], pb[ok]
            e = np.stack([EG[p[:, 0], p[:, 1], p[:, 2], a], EG[p[:, 0], p[:, 1], p[:, 2], b], EG[pa[:, 0], pa[:, 1], pa[:, 2], b], EG[pb[:, 0], pb[:, 1], pb[:, 2], a]], 1)
            good = (e >= 0).all(axis=1); e = e[good]; cs = cl[e]
            for x in range(4):
                for y in range(x + 1, 4):
                    np.add.at(J, (cs[:, x], cs[:, y]), 1); npairs += len(cs)
    J = J + J.T; J /= max(J.sum(), 1)
    with np.errstate(divide='ignore', invalid='ignore'):
        C = J / np.outer(f, f)
    return C, npairs

def plaquettes_with_edges(tiles, level):
    """Like fe.plaquettes but also returns the lattice edge (point, axis) of every inter-tile plaquette."""
    N = 2 ** (level + 1)
    G = np.array([t[0] for t in tiles])
    grid = -np.ones((N, N, N), int)
    for a, (_, _, cs) in enumerate(tiles):
        for c in cs: grid[c] = a
    own_all, code_all, edge_all = [], [], []
    for d in range(3):
        a_, b_ = [x for x in range(3) if x != d]
        P = np.stack(np.meshgrid(np.arange(N + 1), np.arange(N + 1), np.arange(N + 1), indexing='ij'), -1).reshape(-1, 3)
        ea = np.zeros(3, int); ea[a_] = 1; eb = np.zeros(3, int); eb[b_] = 1
        corners = [P, P - ea, P - ea - eb, P - eb]
        ok = np.ones(len(P), bool)
        for c in corners: ok &= ((c >= 0) & (c < N)).all(axis=1)
        Pk = P[ok]; corners = [c[ok] for c in corners]
        owners = np.stack([grid[c[:, 0], c[:, 1], c[:, 2]] for c in corners], 1)
        present = (owners >= 0).all(axis=1); owners = owners[present]; Pk = Pk[present]
        hol = np.zeros(len(owners), int)
        for (i, j, ax) in ((0, 1, a_), (1, 2, b_), (2, 3, a_), (3, 0, b_)):
            nvec = np.zeros(3, int); nvec[ax] = 1
            oa, ob = owners[:, i], owners[:, j]
            ua = np.einsum('ikj,k->ij', G[oa], nvec); ub = np.einsum('ikj,k->ij', G[ob], nvec)
            lc = fe.link_codes(ua, ub); lc = np.where(oa == ob, 0, lc); hol = fe.MUL[hol, lc]
        inter = ~((owners == owners[:, :1]).all(axis=1))
        own_all.append(owners[inter]); code_all.append(hol[inter]); edge_all.append(np.c_[Pk[inter], np.full(inter.sum(), d)])
    return np.concatenate(own_all), np.concatenate(code_all), np.concatenate(edge_all), grid, G

def ring_loops(grid, G, N, shape):
    """Holonomy classes of loops around a shape x shape block of parallel lattice edges (shape 1 = plaquette, 2 = 2x2 square)
    and, for shape=(2,1), a 2x1 rectangle.  Returns class fractions (+1, -1, traceless) over inter-tile loops."""
    sa, sb = shape
    tot = np.zeros(3, int)
    for d in range(3):
        a_, b_ = [x for x in range(3) if x != d]
        ea = np.zeros(3, int); ea[a_] = 1; eb = np.zeros(3, int); eb[b_] = 1
        # ring of cubes around the block of edges with points p + i e_a + j e_b, 0<=i<sa, 0<=j<sb:
        # cubes with offsets (i, j) in the (sa+1) x (sb+1) block of lower corners p - e_a - e_b + i e_a + j e_b, i in 0..sa, j in 0..sb,
        # minus the interior; traverse the ring counter-clockwise.
        ring = [(i, 0) for i in range(sa + 1)] + [(sa, j) for j in range(1, sb + 1)] + [(i, sb) for i in range(sa - 1, -1, -1)] + [(0, j) for j in range(sb - 1, 0, -1)]
        P = np.stack(np.meshgrid(np.arange(N + 1), np.arange(N + 1), np.arange(N + 1), indexing='ij'), -1).reshape(-1, 3)
        base = P - ea - eb
        corners = [base + i * ea + j * eb for (i, j) in ring]
        ok = np.ones(len(P), bool)
        for c in corners: ok &= ((c >= 0) & (c < N)).all(axis=1)
        corners = [c[ok] for c in corners]
        owners = np.stack([grid[c[:, 0], c[:, 1], c[:, 2]] for c in corners], 1)
        present = (owners >= 0).all(axis=1); owners = owners[present]
        hol = np.zeros(len(owners), int); R = len(ring)
        for q in range(R):
            i0, j0 = ring[q]; i1, j1 = ring[(q + 1) % R]
            ax = a_ if i1 != i0 else b_
            nvec = np.zeros(3, int); nvec[ax] = 1
            oa, ob = owners[:, q], owners[:, (q + 1) % R]
            ua = np.einsum('ikj,k->ij', G[oa], nvec); ub = np.einsum('ikj,k->ij', G[ob], nvec)
            lc = fe.link_codes(ua, ub); lc = np.where(oa == ob, 0, lc); hol = fe.MUL[hol, lc]
        inter = ~((owners == owners[:, :1]).all(axis=1)); hol = hol[inter]
        cl = fe.classes(hol); tot += np.bincount(cl, minlength=3)
    return tot / max(tot.sum(), 1)

def predictors(tiles, level):
    n = len(tiles); N = 2 ** (level + 1)
    owners, hol, edges, grid, G = plaquettes_with_edges(tiles, level)
    cl = fe.classes(hol); m = len(hol)
    out = {'N_inter': int(m), 'n_plus': int((cl == 0).sum()), 'n_minus': int((cl == 1).sum()), 'n_traceless': int((cl == 2).sum())}
    # axis-resolved counts (Q8-gauge invariant only): codes 2,3 -> axis 0 (i), 4,5 -> j, 6,7 -> k
    for ax, nm in enumerate('ijk'): out[f'n_{nm}'] = int(((hol == 2 + 2 * ax) | (hol == 3 + 2 * ax)).sum())
    out['f_m1'] = out['n_minus'] / m; out['f_trl'] = out['n_traceless'] / m; out['f_nontriv'] = 1 - out['n_plus'] / m
    for nm in 'ijk': out[f'f_{nm}'] = out[f'n_{nm}'] / m
    # depth enrichments
    for d in (1, 2, 3):
        if d > level: continue
        A = anc(owners, level, d); strad = ~((A == A[:, :1]).all(axis=1)); p_all = strad.mean()
        out[f'strad{d}_all'] = float(p_all)
        for nm, k in (('m1', 1), ('trl', 2)):
            sel = cl == k
            out[f'enr{d}_{nm}'] = float(strad[sel].mean() / p_all) if sel.any() and p_all > 0 else float('nan')
    # per-tile counts
    o = np.sort(owners, axis=1); dist = np.ones_like(o, bool); dist[:, 1:] = o[:, 1:] != o[:, :-1]
    for nm, k in (('m1', 1), ('trl', 2), ('nt', None)):
        sel = (cl != 0) if k is None else (cl == k)
        cnt = np.zeros(n, int); np.add.at(cnt, o[sel][dist[sel]], 1)
        out[f'cv_{nm}'] = float(cnt.std() / cnt.mean()) if cnt.mean() > 0 else float('nan')
        if nm == 'm1':
            for d in (1, 2):
                if d > level: continue
                per_child = np.bincount(np.arange(n) // 8 ** (level - d), weights=cnt, minlength=8 ** d)
                out[f'hvar{d}_m1'] = float(per_child.std() / per_child.mean()) if per_child.mean() > 0 else float('nan')
    # nearest-neighbour clustering (as in phase5a_flux_vs_edge) and class-pair correlations
    cnt = np.zeros(n, int); sel = cl == 1; np.add.at(cnt, o[sel][dist[sel]], 1)
    touch = (cnt[o] * dist).sum(axis=1); ntouch = dist.sum(axis=1)
    neigh = (touch - np.where(sel, 1, 0) * ntouch) / ntouch
    out['pair_m1'] = float(neigh[sel].mean() / neigh.mean()) if sel.any() else float('nan')
    Ct = class_pair_stats(owners, cl, n)
    Cp, npairs = panel_pair_stats(owners, cl, edges, N)
    names = ['p1', 'm1', 'trl']
    for a in range(3):
        for b in range(a, 3):
            out[f'Ct_{names[a]}_{names[b]}'] = float(Ct[a, b]); out[f'Cp_{names[a]}_{names[b]}'] = float(Cp[a, b])
    out['n_panel_pairs'] = int(npairs)
    for shape, nm in (((2, 1), 'loop21'), ((2, 2), 'loop22')):
        fr = ring_loops(grid, G, N, shape)
        out[f'{nm}_f_m1'] = float(fr[1]); out[f'{nm}_f_trl'] = float(fr[2])
    return out

# ---------------------------------------------------------------- spectral
def bottom(dec, level, tiles=None):
    tl = tiles if tiles is not None else tiles_at_level(dec, level)
    _, edges = panel_edges(tl); deg = degrees(len(tl), edges); assert deg.max() == 24
    links = clifford_links(tl, edges); H = build_H(len(tl), edges, links, np.full(len(tl), 24.0))
    if level <= 3:
        w, V = sla.eigh(H.toarray(), subset_by_index=(0, 3), driver='evr'); V = V / np.linalg.norm(V, axis=0)
        HV = H @ V; lam = np.real(np.einsum('ij,ij->j', V.conj(), HV)); res = np.linalg.norm(HV - V * lam, axis=0); how = 'dense eigh'
    else:
        lam, V, res, _ = eig_lobpcg(H, 2, extra=2, tol=1e-7); how = 'lobpcg(block=4, tol=1e-7, seed=0)'
    psi = V[:, 0]; p = np.abs(psi[0::2]) ** 2 + np.abs(psi[1::2]) ** 2; p /= p.sum()
    return {'lambda': [float(x) for x in lam[:4]], 'residual': float(max(res[:2])), 'solver': how, 'ipr_n': float((p ** 2).sum() * len(tl)),
            'kramers_split': float(abs(lam[1] - lam[0]))}

# ---------------------------------------------------------------- stages
def shard_path(stage, shard): return os.path.join(RES, f'phase5b_sweep_{stage}_shard{shard}.jsonl')

def run_census(shard, nshards):
    path = shard_path('census', shard); done = set()
    if os.path.exists(path):
        for line in open(path): done.add(json.loads(line)['index'])
    idx = [i for i in range(NDEC) if i % nshards == shard and i not in done]
    print(f"[census shard {shard}/{nshards}] {len(idx)} decorations to do ({len(done)} already)", flush=True)
    t0 = time.time()
    with open(path, 'a') as f:
        for k, i in enumerate(idx):
            dec = decoration(i); t1 = time.time()
            tiles4 = tiles_at_level(dec, 4); pred = predictors(tiles4, 4)
            b3 = bottom(dec, 3)
            rec = {'index': i, 'is_fr30': i == FR30_INDEX, 'decoration': {str(k_): list(v) for k_, v in dec.items()}, 'pred_level': 4, 'pred': pred, 'L3': b3,
                   'seconds': time.time() - t1}
            f.write(json.dumps(rec) + '\n'); f.flush()
            if k % 50 == 0:
                print(f"  {k}/{len(idx)} idx {i}: Y3={b3['lambda'][0]:.5f} f_m1={pred['f_m1']:.4f} f_trl={pred['f_trl']:.4f} enr1_trl={pred['enr1_trl']:.3f} ({time.time()-t0:.0f}s, rss {resource.getrusage(resource.RUSAGE_SELF).ru_maxrss/1e6:.2f} GB)", flush=True)
    print(f"[census shard {shard}] done in {time.time()-t0:.0f}s", flush=True)

def run_level4(shard, nshards):
    S = sample_indices(); path = shard_path('level4', shard); done = set()
    if os.path.exists(path):
        for line in open(path): done.add(json.loads(line)['index'])
    idx = [i for j, i in enumerate(S) if j % nshards == shard and i not in done]
    print(f"[level4 shard {shard}/{nshards}] {len(idx)} decorations ({len(done)} already); sample seed {SAMPLE_SEED}, size {len(S)}", flush=True)
    t0 = time.time()
    with open(path, 'a') as f:
        for k, i in enumerate(idx):
            dec = decoration(i); t1 = time.time(); b4 = bottom(dec, 4)
            f.write(json.dumps({'index': i, 'L4': b4, 'seconds': time.time() - t1}) + '\n'); f.flush()
            if k % 25 == 0: print(f"  {k}/{len(idx)} idx {i}: Y4={b4['lambda'][0]:.5f} res={b4['residual']:.1e} ({time.time()-t0:.0f}s)", flush=True)
    print(f"[level4 shard {shard}] done in {time.time()-t0:.0f}s", flush=True)

def merge():
    recs = {}
    for fn in sorted(os.listdir(RES)):
        if fn.startswith('phase5b_sweep_census_shard'):
            for line in open(os.path.join(RES, fn)):
                r = json.loads(line); recs[r['index']] = r
    for fn in sorted(os.listdir(RES)):
        if fn.startswith('phase5b_sweep_level4_shard'):
            for line in open(os.path.join(RES, fn)):
                r = json.loads(line)
                if r['index'] in recs: recs[r['index']]['L4'] = r['L4']
    out = {'n_census': len(recs), 'fr30_index': FR30_INDEX, 'sample_seed': SAMPLE_SEED, 'sample': sample_indices(),
           'records': [recs[i] for i in sorted(recs)]}
    with open(os.path.join(RES, 'phase5b_sweep.json'), 'w') as f: json.dump(out, f)
    print(f"merged {len(recs)} census records, {sum('L4' in r for r in recs.values())} with level-4 bottoms -> audit/results/phase5b_sweep.json")

# ---------------------------------------------------------------- analysis
PRIMARY = ['enr1_trl', 'cv_m1', 'pair_m1']
EXPLORATORY = ['enr1_m1', 'enr2_m1', 'enr2_trl', 'enr3_m1', 'enr3_trl', 'cv_trl', 'cv_nt', 'hvar1_m1', 'hvar2_m1',
               'Ct_p1_p1', 'Ct_p1_m1', 'Ct_p1_trl', 'Ct_m1_m1', 'Ct_m1_trl', 'Ct_trl_trl',
               'Cp_p1_p1', 'Cp_p1_m1', 'Cp_p1_trl', 'Cp_m1_m1', 'Cp_m1_trl', 'Cp_trl_trl',
               'loop21_f_m1', 'loop21_f_trl', 'loop22_f_m1', 'loop22_f_trl', 'f_i', 'f_j', 'f_k']

def ols(X, y):
    coef, *_ = np.linalg.lstsq(X, y, rcond=None); return coef

def cv_r2(X, y, folds):
    pred = np.empty_like(y)
    for tr, te in folds:
        c = ols(X[tr], y[tr]); pred[te] = X[te] @ c
    ss = ((y - pred) ** 2).sum(); return 1 - ss / ((y - y.mean()) ** 2).sum(), np.sqrt(ss / len(y))

def kfold(n, k, seed):
    rng = np.random.default_rng(seed); perm = rng.permutation(n); fold = np.array_split(perm, k)
    return [(np.setdiff1d(perm, te), te) for te in fold]

def analyze():
    D = json.load(open(os.path.join(RES, 'phase5b_sweep.json'))); recs = D['records']
    lines = []
    P = lambda s='': (print(s), lines.append(s))
    P("PHASE V-B, WORKSTREAM B: CENSUS OF ADMISSIBLE CHAIR DECORATIONS AND PREREGISTERED PREDICTOR ANALYSIS")
    P("All numbers computed by audit/phase5b_sweep.py (protocol in the module docstring; fixed before inspection).")
    P(f"census records: {len(recs)} of {NDEC}; FR30 index {FR30_INDEX}")
    def table(recs, ykey, label):
        X0 = np.array([[1, r['pred']['f_trl'], r['pred']['f_m1']] for r in recs]); y = np.array([r[ykey]['lambda'][0] for r in recs])
        fr = [k for k, r in enumerate(recs) if r['is_fr30']]; fr = fr[0] if fr else None
        n = len(y); folds = kfold(n, 10, FOLD_SEED)
        P(); P(f"=== outcome {label} (n={n}) ===")
        P(f" Y range [{y.min():.4f}, {y.max():.4f}], mean {y.mean():.4f}, sd {y.std():.4f}; distinct values (6 dp): {len(np.unique(np.round(y, 6)))}")
        if fr is not None: P(f" FR30: Y={y[fr]:.5f}, rank {int((y > y[fr]).sum()) + 1} of {n} (1 = highest); number above FR30: {int((y > y[fr]).sum())}")
        c0 = ols(X0, y); r2in = 1 - ((y - X0 @ c0) ** 2).sum() / ((y - y.mean()) ** 2).sum(); cvr2, cvrmse = cv_r2(X0, y, folds)
        P(f" flux baseline Y ~ {c0[0]:.3f} + {c0[1]:.3f} f_trl + {c0[2]:.3f} f_m1: in-sample R^2 {r2in:.4f}, 10-fold CV R^2 {cvr2:.4f}, CV-RMSE {cvrmse:.4f}")
        res0 = y - X0 @ c0
        if fr is not None: P(f" FR30 flux-baseline residual {res0[fr]:+.4f} = {res0[fr]/res0.std():+.2f} sd; residual rank {int((res0 > res0[fr]).sum()) + 1} of {n}")
        rng = np.random.default_rng(FOLD_SEED)
        rows = []
        for kind, names, alpha in (('PRIMARY', PRIMARY, 0.05 / len(PRIMARY)), ('EXPLORATORY', EXPLORATORY, 0.05 / len(EXPLORATORY))):
            P(f" --- {kind} predictors (alpha = {alpha:.4f}) ---")
            P(f" {'predictor':<14} {'corr(Y)':>8} {'corr(f_m1)':>10} {'corr(f_trl)':>11} {'VIF':>7} {'partial b (sd units)':>20} {'dCV-R2':>8} {'perm p':>7} {'FR30 value':>10} {'FR30 pct':>8}")
            for nm in names:
                x = np.array([r['pred'].get(nm, np.nan) for r in recs], float)
                if np.isnan(x).any() or x.std() == 0: P(f" {nm:<14} (missing or constant)"); continue
                X1 = np.c_[X0, x]; c1 = ols(X1, y); cv1, _ = cv_r2(X1, y, folds); d = cv1 - cvr2
                # VIF of x against flux
                cx = ols(X0, x); r2x = 1 - ((x - X0 @ cx) ** 2).sum() / ((x - x.mean()) ** 2).sum(); vif = 1 / max(1 - r2x, 1e-12)
                # permutation test on the CV-R2 improvement
                cnt = 0
                for _ in range(NPERM):
                    xp = rng.permutation(x); cvp, _ = cv_r2(np.c_[X0, xp], y, folds)
                    if cvp - cvr2 >= d: cnt += 1
                pperm = (cnt + 1) / (NPERM + 1)
                fv = x[fr] if fr is not None else np.nan; pct = (x < fv).mean() * 100 if fr is not None else np.nan
                flag = ' *' if pperm < alpha else ''
                P(f" {nm:<14} {np.corrcoef(x, y)[0,1]:+8.3f} {np.corrcoef(x, X0[:,2])[0,1]:+10.3f} {np.corrcoef(x, X0[:,1])[0,1]:+11.3f} {vif:7.2f} {c1[3]*x.std()/y.std():+20.3f} {d:+8.4f} {pperm:7.3f} {fv:10.4f} {pct:8.1f}{flag}")
                rows.append((nm, d, pperm))
        # forward selection with nested CV (greedy on CV-R2, stop when improvement < 0.002)
        chosen = []; Xc = X0.copy(); base = cvr2
        pool = [nm for nm in PRIMARY + EXPLORATORY if not np.isnan([r['pred'].get(nm, np.nan) for r in recs]).any()]
        while True:
            best = None
            for nm in pool:
                if nm in chosen: continue
                x = np.array([r['pred'][nm] for r in recs], float)
                if x.std() == 0: continue
                cv1, _ = cv_r2(np.c_[Xc, x], y, folds)
                if best is None or cv1 > best[1]: best = (nm, cv1)
            if best is None or best[1] - base < 0.002: break
            chosen.append(best[0]); Xc = np.c_[Xc, np.array([r['pred'][best[0]] for r in recs], float)]; base = best[1]
        P(f" greedy forward selection on CV-R^2 (stop at +0.002): {chosen} -> CV R^2 {base:.4f} (baseline {cvr2:.4f})")
        if chosen and fr is not None:
            cc = ols(Xc, y); resc = y - Xc @ cc
            P(f" FR30 residual under flux + {chosen}: {resc[fr]:+.4f} ({resc[fr]/resc.std():+.2f} sd); rank {int((resc > resc[fr]).sum()) + 1} of {n}")
        return y, X0
    y3, X0 = table(recs, 'L3', 'Y3 = level-3 pinned bottom (all decorations)')
    recs4 = [r for r in recs if 'L4' in r]
    if recs4:
        y4, _ = table(recs4, 'L4', 'Y4 = level-4 pinned bottom (preregistered sample)')
        y3s = np.array([r['L3']['lambda'][0] for r in recs4])
        P(f" corr(Y3, Y4) over the sample: {np.corrcoef(y3s, y4)[0,1]:.4f}; mean drop Y3-Y4 {np.mean(y3s - y4):.4f} (sd {np.std(y3s - y4):.4f})")
        resid = [r['L4']['residual'] for r in recs4]; P(f" level-4 residual max {max(resid):.1e}")
    # exact flux-matched groups
    P(); P("=== exact flux-matched groups (identical level-4 class-count vectors) ===")
    groups = {}
    for r in recs:
        key = (r['pred']['n_plus'], r['pred']['n_minus'], r['pred']['n_i'], r['pred']['n_j'], r['pred']['n_k'])
        groups.setdefault(key, []).append(r)
    sizes = sorted((len(v) for v in groups.values()), reverse=True)
    P(f" {len(groups)} distinct class-count vectors; group sizes (top 10): {sizes[:10]}; singletons: {sum(s == 1 for s in sizes)}")
    big = [(k, v) for k, v in groups.items() if len(v) >= 4]
    spreads = [np.ptp([r['L3']['lambda'][0] for r in v]) for _, v in big]
    if spreads: P(f" groups with >= 4 members: {len(big)}; within-group spread of Y3: median {np.median(spreads):.4f}, max {max(spreads):.4f}; total sd of Y3 {y3.std():.4f}")
    frk = next(k for k, v in groups.items() if any(r['is_fr30'] for r in v))
    g = groups[frk]; P(f" FR30's exact class-count vector {frk} is shared by {len(g)} decoration(s); their Y3: {sorted(round(r['L3']['lambda'][0], 5) for r in g)}")
    # within-group analysis of structural predictors (flux held exactly fixed)
    for nm in PRIMARY + ['Ct_m1_m1', 'Cp_trl_trl', 'loop22_f_m1']:
        xs, ys = [], []
        for _, v in big:
            x = np.array([r['pred'][nm] for r in v]); yy = np.array([r['L3']['lambda'][0] for r in v])
            if x.std() == 0 or yy.std() == 0: continue
            xs.append(x - x.mean()); ys.append(yy - yy.mean())
        if xs:
            xs = np.concatenate(xs); ys = np.concatenate(ys)
            P(f" within exact-flux groups: corr({nm}, Y3) = {np.corrcoef(xs, ys)[0,1]:+.3f} over {len(xs)} decorations in {len(big)} groups")
    with open(os.path.join(RES, 'phase5b_sweep_analysis.txt'), 'w') as f: f.write('\n'.join(lines) + '\n')

if __name__ == '__main__':
    os.environ.setdefault('OMP_NUM_THREADS', '1')
    cmd = sys.argv[1]
    if cmd == 'census': run_census(int(sys.argv[2]), int(sys.argv[3]))
    elif cmd == 'level4': run_level4(int(sys.argv[2]), int(sys.argv[3]))
    elif cmd == 'merge': merge()
    elif cmd == 'analyze': analyze()
    elif cmd == 'selftest':
        t = time.time(); tiles = tiles_at_level(FR30, 4); pr = predictors(tiles, 4)
        print({k: (round(v, 4) if isinstance(v, float) else v) for k, v in pr.items()}); print('predictors', round(time.time() - t, 1), 's')
        t = time.time(); print(bottom(FR30, 3), round(time.time() - t, 1), 's')
        print('FR30 index', FR30_INDEX, 'sample head', sample_indices()[:5])
