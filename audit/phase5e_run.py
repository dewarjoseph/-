#!/usr/bin/env python3
"""Phase V-E pipeline (protocol: deliverables/PHASE5E_PROTOCOL.md, audit/results/phase5e_protocol.json, frozen before any
evaluation-set value was computed).  Stages (each resumable, one JSON line per system):

  level4 <shard> <nshards>   the 264 V-D rule classes + 18 V-D controls (+ 4 development rules) at level 4: exact ground pair
                             (shift-invert at 0, H >= 0), gap, every frozen basis configuration (root E_W, iterations, seconds,
                             captured weight c, Ritz defect g_W(E_0)), tile support of psi_S, exploratory energy budget,
                             exact Schur root on the validation subset.  Densities -> phase5e_density_L4.npz (adaptive stage).
  level3 <shard> <nshards>   the same 264 classes at level 3 (every family; exact eigh)
  levels <system>            the level sweep L = 2..5 (fixed family parameters, so fixed retained dimension D across L)
  adaptive <shard> <nshards> training-only tile selection: V-D CV repetition 0 folds; tiles ranked by the mean ground-state
                             density of the TRAINING rules (geometric tile keys); controls use all 264 rules
  gauge                      random SU(2) gauge per tile: every family at levels 3 and 4 on the gauge-test set
Usage: python -u -I audit/phase5e_run.py <stage> [...]
"""
import os, sys, time, json
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); RES = os.path.join(HERE, 'results')
os.environ.setdefault('OMP_NUM_THREADS', '1')
import numpy as np, scipy.linalg as sla
import phase5e_rg as rg, phase5d_schur as d
from independent_clifford_q8_audit import FR30

DEV_RULES = [950, 1583, 1787, 3133]            # one representative per class outside the 264 evaluation classes, seed 20261026
REFERENCE = ['fr30', 3697, 1387, 2238] + DEV_RULES
ADAPT_M = [64, 128, 229, 512]                    # tiles kept (D = 2m); 229 tiles = the largest D <= 10% of dim S at level 4
CV_SEED0 = 20261024
def log(*a): print(*a, flush=True)

def spec_of(name):
    if name == 'fr30': return FR30
    if isinstance(name, int): return name
    if name.startswith('dec'): return int(name[3:])
    return name

def systems():
    """evaluation rules (V-D order: sorted by census index) and controls with their stored level-4 bottoms."""
    recs = []
    for k in range(3):
        for l in open(os.path.join(RES, f'phase5d_features_shard{k}.jsonl')): r = json.loads(l); recs.append(r)
    recs = sorted(recs, key=lambda r: r['index'])
    rules = [{'name': ('fr30' if r['is_fr30'] else int(r['index'])), 'index': int(r['index']), 'Y4': r['Y4'], 'Y3': r['Y3'], 'kind': 'rule'} for r in recs]
    ctl = [json.loads(l) for l in open(os.path.join(RES, 'phase5d_controls.jsonl'))]
    controls = [{'name': c['system'], 'Y4': c['Y4'], 'kind': 'control'} for c in ctl]
    dev = [{'name': i, 'index': i, 'Y4': None, 'kind': 'dev'} for i in DEV_RULES]
    return rules, controls, dev

# Compute-only deviation (recorded in the report): at level 4 the evaluation systems use the grid capped at D <~ 600, decided
# before any level-4 evaluation system had completed.  The full grid is kept for the development rules and the level sweep.
LEVEL4_DROP = {('child', 64), ('face', 16), ('fec', 8), ('fec', 16), ('patch2', 8), ('patch3', 2), ('iface2', 32)}
def configs(full=True):
    out = [(f, k) for f, ks in rg.FAMILIES.items() for k in ks if full or (f, k) not in LEVEL4_DROP]
    return out + [('interface', None)]

# ------------------------------------------------------------------ per-system analysis
def support_stats(s, psi):
    p = np.abs(psi[0::2, 0]) ** 2 + np.abs(psi[1::2, 0]) ** 2 + np.abs(psi[0::2, 1]) ** 2 + np.abs(psi[1::2, 1]) ** 2; p /= p.sum()
    pS = p[s.Sall]; wS = float(pS.sum()); q = np.sort(pS)[::-1] / pS.sum(); cs = np.cumsum(q)
    cls = {}
    for c in range(8):
        for t, (k, _) in zip(s.S[c], s.tile_class(c)): cls[k] = cls.get(k, 0.0) + p[t]
    out = {'S_weight': wS, 'class_weight': {k: float(v) for k, v in cls.items()}, 'ipr_n': float((p ** 2).sum() * s.n)}
    for f in (0.5, 0.9, 0.99, 0.999): out[f'tiles_{f}'] = int(np.searchsorted(cs, f) + 1)
    out['S_tiles'] = int(len(s.Sall)); out['interface_tiles'] = int(sum(1 for t in s.Sall if s.F[t]))
    return out, p

def energy_budget(s, psi, E0):
    """EXPLORATORY gauge-invariant decomposition of E_0 = <psi, H psi>: child-internal energies and seam (inter-child) bond energies,
    with the bond efficiency eta = -(bond energy)/(2 sum_panels |psi_a||psi_b|) (eta = 1: no frustration of the hopping)."""
    v = psi[:, 0] / np.linalg.norm(psi[:, 0]); H = s.H.tocoo(); r, c, x = H.row, H.col, H.data
    ta, tb = r // 2, c // 2; ca, cb = s.child[ta], s.child[tb]
    contrib = np.conj(v[r]) * x * v[c]
    amp = np.sqrt(np.abs(v[0::2]) ** 2 + np.abs(v[1::2]) ** 2)
    inter = ca != cb; offd = (ta != tb)
    seam_E = float(np.real(contrib[inter].sum())); intra_E = float(np.real(contrib[~inter].sum()))
    # magnitude scale of the hopping: sum over panels |psi_a||psi_b| (each panel appears twice in H as a 2x2 block pair; count via edges)
    a = np.array([e[0] for e in s.edges]); b = np.array([e[1] for e in s.edges]); cross = s.child[a] != s.child[b]
    mag = amp[a] * amp[b]
    hop_intra = float(np.real(contrib[offd & ~inter].sum()))
    out = {'E_check': seam_E + intra_E, 'seam_energy': seam_E, 'intra_hop_energy': hop_intra, 'diag_energy': float(np.real(contrib[~offd].sum())),
           'seam_eff': float(-seam_E / (2 * mag[cross].sum())) if mag[cross].sum() > 0 else float('nan'),
           'intra_eff': float(-hop_intra / (2 * mag[~cross].sum())), 'seam_mag': float(2 * mag[cross].sum()), 'intra_mag': float(2 * mag[~cross].sum())}
    return out

def analyse_system(entry, level, cfgs, exact=False, keep_psi=False):
    t0 = time.time(); s = rg.System(spec_of(entry['name']), level)
    ww, psi = rg.ground_state(s); E0 = float(ww[0])
    distinct = [x for x in ww[1:] if x - ww[0] > 1e-7]
    gap = float(distinct[0] - ww[0]) if distinct else float('nan')         # next distinct level (second Kramers pair)
    sup, p = support_stats(s, psi)
    rec = {'name': entry['name'], 'kind': entry['kind'], 'level': level, 'n': s.n, 'E0': E0, 'gap': gap, 'lam_II': s.lam_II, 'dimS': int(s.offs[-1]),
           'build_s': s.build_seconds, 'support': sup, 'budget': energy_budget(s, psi, E0), 'bases': {}}
    if entry.get('Y4') is not None and level == 4: rec['Y4_stored'] = entry['Y4']; rec['E0_minus_stored'] = E0 - entry['Y4']
    for fam, k in cfgs:
        t1 = time.time()
        try: P = rg.make_basis(s, fam, k)
        except Exception as ex: rec['bases'][f'{fam}:{k}'] = {'error': repr(ex)}; continue
        red = rg.Reduced(s, P); E, it = red.root(); tb = time.time() - t1
        cap, _ = rg.captured(s, red, psi); gd = red.g(E0) if red.D else float('nan')
        rec['bases'][f'{fam}:{k}'] = {'D': red.D, 'E_W': E, 'err': (E - E0) if E == E else None, 'it': it, 'nev': red.nev, 'seconds': tb, 'capture': cap, 'ritz_defect': gd}
    if exact:
        t1 = time.time(); red = rg.Reduced(s, rg.P_exact(s)); E, it = red.root()
        rec['exact'] = {'D': red.D, 'E_W': E, 'err': E - E0, 'it': it, 'seconds': time.time() - t1}
    rec['seconds'] = time.time() - t0
    if keep_psi: np.save(os.path.join(RES, f"phase5e_psi_{entry['name']}_L{level}.npy"), psi.astype(np.complex128))
    return rec, p

def done_names(path):
    out = set()
    if os.path.exists(path):
        for l in open(path):
            try: out.add(str(json.loads(l)['name']))
            except json.JSONDecodeError: pass
    return out

def run_level(level, shard, nshards):
    rules, controls, dev = systems(); allsys = rules + controls + (dev if level == 4 else [])
    if level == 3: allsys = rules
    path = os.path.join(RES, f'phase5e_L{level}_shard{shard}.jsonl'); done = done_names(path)
    todo = [e for j, e in enumerate(allsys) if j % nshards == shard and str(e['name']) not in done]
    dens_path = os.path.join(RES, f'phase5e_density_L{level}_shard{shard}.npz')
    dens = dict(np.load(dens_path)) if os.path.exists(dens_path) else {}
    log(f"[L{level} shard {shard}/{nshards}] {len(todo)} systems to do ({len(done)} done)")
    with open(path, 'a') as f:
        for j, e in enumerate(todo):
            exact = level == 4 and (e['name'] == 'fr30' or (e['kind'] == 'rule' and e['index'] % 20 == 0) or e['kind'] == 'dev')
            rec, p = analyse_system(e, level, configs(full=(level != 4 or e['kind'] == 'dev')), exact=exact, keep_psi=(level == 4 and (e['name'] in REFERENCE)))
            if 'Y4' in e and e['Y4'] is not None and level == 3: rec['Y3_stored'] = e['Y3']; rec['E0_minus_stored'] = rec['E0'] - e['Y3']
            f.write(json.dumps(rec) + '\n'); f.flush()
            dens[str(e['name'])] = p.astype(np.float32); np.savez(dens_path, **dens)
            b = rec['bases']
            log(f"  {j}/{len(todo)} {e['name']}: E0 {rec['E0']:.6f} dE0 {rec.get('E0_minus_stored', 0):+.1e} | child16 {b.get('child:16',{}).get('err')} face4 {b.get('face:4',{}).get('err')} "
                f"iface2:8 {b.get('iface2:8',{}).get('err')} interface {b.get('interface:None',{}).get('err')} ({rec['seconds']:.0f}s)")

# ------------------------------------------------------------------ level sweep
def run_levels(name, levels=(2, 3, 4, 5)):
    spec = name if name == 'fr30' else int(name)
    path = os.path.join(RES, 'phase5e_levels.jsonl')
    done = set()
    if os.path.exists(path):
        for l in open(path): r = json.loads(l); done.add((str(r['name']), r['level']))
    with open(path, 'a') as f:
        for L in levels:
            if (str(spec), L) in done: continue
            cfgs = [c for c in configs() if not (L == 5 and c[0] == 'interface')]
            rec, p = analyse_system({'name': spec, 'kind': 'reference'}, L, cfgs, exact=(L <= 3), keep_psi=(L == 5))
            f.write(json.dumps(rec) + '\n'); f.flush()
            log(f"[levels {name} L{L}] E0 {rec['E0']:.7f} gap {rec['gap']:.2e} ({rec['seconds']:.0f}s)")

def child_cluster(name, levels=(1, 2, 3, 4)):
    """low spectrum of the supertile surface response R_m(E_REF) (the object the recursion iterates): counts within windows."""
    spec = FR30 if name == 'fr30' else int(name); out = []
    for m in levels:
        tiles = d.tiles_of(spec, m); H, edges = d.build(tiles); n = len(tiles); deg = d.degrees(n, edges); surf = deg < 24
        s_, i_ = np.nonzero(surf)[0], np.nonzero(~surf)[0]; ss, ii = d.spinor(s_), d.spinor(i_); Hd = H.toarray()
        R = Hd[np.ix_(ss, ss)] - rg.E_REF * np.eye(len(ss))
        if len(ii): R -= Hd[np.ix_(ss, ii)] @ sla.solve(Hd[np.ix_(ii, ii)] - rg.E_REF * np.eye(len(ii)), Hd[np.ix_(ii, ss)], assume_a='her')
        w = np.linalg.eigvalsh(R)
        out.append({'m': m, 'dim': int(len(ss)), 'lowest': w[:6].tolist(), 'count_within': {str(x): int((w < w[0] + x).sum()) for x in (0.25, 0.5, 1, 2, 4)},
                    'spread': float(w[-1] - w[0])})
        log(f"[cluster {name} m={m}] dim {len(ss)} lowest {np.round(w[:4], 4)} counts {out[-1]['count_within']}")
    return out

# ------------------------------------------------------------------ adaptive (training-only) tile selection
def load_density(level=4):
    D = {}
    for fn in sorted(os.listdir(RES)):
        if fn.startswith(f'phase5e_density_L{level}_shard') and fn.endswith('.npz'): D.update(dict(np.load(os.path.join(RES, fn))))
    return D

def depth_bonds(s, psi):
    """EXPLORATORY exact hierarchical energy decomposition E_0 = 24 + sum_d B_d, B_d = bond energy <psi, -A_d psi> of the panels whose
    two tiles have their lowest common ancestor at depth d (d = 0: different depth-1 children, i.e. the top seams; d = L-1: siblings
    inside one level-1 supertile).  M_d = 2 sum_{panels at depth d} |psi_a||psi_b| bounds -B_d; eta_d = -B_d/M_d (gauge invariant)."""
    v = psi[:, 0] / np.linalg.norm(psi[:, 0]); L = s.level; H = s.H.tocoo(); ta, tb = H.row // 2, H.col // 2; off = ta != tb
    def lca(a, b):
        out = np.full(len(a), -1)
        for dd in range(L):
            same = (a // 8 ** (L - dd)) == (b // 8 ** (L - dd)); out[same] = dd
        return out
    contrib = np.real(np.conj(v[H.row]) * H.data * v[H.col]); dl = lca(ta, tb)
    amp = np.sqrt(np.abs(v[0::2]) ** 2 + np.abs(v[1::2]) ** 2); a = np.array([e[0] for e in s.edges]); b = np.array([e[1] for e in s.edges]); de = lca(a, b)
    out = {'diag': float(contrib[~off].sum())}
    for dd in range(L):
        out[str(dd)] = {'B': float(contrib[off & (dl == dd)].sum()), 'M': float(2 * (amp[a] * amp[b])[de == dd].sum()), 'panels': int((de == dd).sum())}
    return out

def run_adaptive(shard, nshards, level=4):
    rules, controls, _ = systems(); dens = load_density(level); n = len(rules)
    names = [str(r['name']) for r in rules]; assert all(nm in dens for nm in names), 'densities missing: run the level4 stage first'
    # geometric keys of every system (tile order differs between rules; the tiling itself does not)
    def keys_of(name): return [rg.geo_key(t) for t in d.tiles_of(spec_of(name), level)]
    ref_keys = keys_of('fr30'); kpos = {k: i for i, k in enumerate(ref_keys)}
    def to_ref(name, p):
        out = np.zeros(len(p)); ks = keys_of(name); out[[kpos[k] for k in ks]] = p; return out
    cache = os.path.join(RES, f'phase5e_density_geo_L{level}.npy')
    if os.path.exists(cache): G = np.load(cache)
    else:
        G = np.array([to_ref(nm, dens[nm]) for nm in names]); np.save(cache, G)
    rng = np.random.default_rng(CV_SEED0); perm = rng.permutation(n); folds = np.array_split(perm, 10)
    fold_of = np.empty(n, int)
    for fi, te in enumerate(folds): fold_of[te] = fi
    path = os.path.join(RES, f'phase5e_adaptive_L{level}_shard{shard}.jsonl'); done = done_names(path)
    todo = [(j, e) for j, e in enumerate(rules + controls) if j % nshards == shard and str(e['name']) not in done]
    log(f"[adaptive shard {shard}] {len(todo)} systems")
    with open(path, 'a') as f:
        for j, e in todo:
            tr = np.nonzero(fold_of != fold_of[j])[0] if j < n else np.arange(n)
            score = G[tr].mean(0)
            s = rg.System(spec_of(e['name']), level); ks = rg.geo_keys(s); geo2loc = np.array([kpos[k] for k in ks])
            sc_loc = score[geo2loc]; surf = np.zeros(s.n, bool); surf[s.Sall] = True
            w, psi = rg.ground_state(s); E0 = float(w[0])
            own = np.abs(psi[0::2, 0]) ** 2 + np.abs(psi[1::2, 0]) ** 2
            rec = {'name': e['name'], 'kind': e['kind'], 'fold': int(fold_of[j]) if j < n else -1, 'E0': E0, 'bases': {}, 'bonds': depth_bonds(s, psi)}
            for m in ADAPT_M:
                for tag, sc in (('adaptive', sc_loc), ('oracle', own)):
                    order = np.argsort(-np.where(surf, sc, -np.inf)); mask = np.zeros(s.n, bool); mask[order[:m]] = True
                    t1 = time.time(); red = rg.Reduced(s, rg.P_tiles(s, mask)); E, it = red.root(); cap, _ = rg.captured(s, red, psi)
                    rec['bases'][f'{tag}:{m}'] = {'D': red.D, 'E_W': E, 'err': (E - E0) if E == E else None, 'it': it, 'seconds': time.time() - t1, 'capture': cap}
            f.write(json.dumps(rec) + '\n'); f.flush()
            log(f"  {e['name']}: adaptive:229 {rec['bases']['adaptive:229']['err']} oracle:229 {rec['bases']['oracle:229']['err']} adaptive:512 {rec['bases']['adaptive:512']['err']}")

# ------------------------------------------------------------------ gauge test
def run_gauge():
    out = []
    for L, names in ((3, ['fr30', 3697, 1387, 2238, 'iid1', 'shuffle1', 'flip1,0.05', 'dec2159'] + DEV_RULES), (4, ['fr30', 1387, 'iid1', 950])):
        for nm in names:
            spec = spec_of(nm); s0 = rg.System(spec, L); s1 = rg.System(spec, L, gauge_seed=11); dev = {}
            for fam, k in configs() + [('exact', None)]:
                if L == 4 and (fam == 'exact' or (fam in ('child',) and k == 64) or fam == 'interface'): continue
                e0 = rg.Reduced(s0, rg.make_basis(s0, fam, k)).root()[0]; e1 = rg.Reduced(s1, rg.make_basis(s1, fam, k)).root()[0]
                dev[f'{fam}:{k}'] = abs(e0 - e1) if (e0 == e0 and e1 == e1) else (0.0 if e0 != e0 and e1 != e1 else float('inf'))
            rec = {'level': L, 'name': nm, 'max_dev': max(dev.values()), 'dev': dev}; out.append(rec)
            log(f"[gauge L{L} {nm}] max |dE_W| = {rec['max_dev']:.2e}")
    json.dump(out, open(os.path.join(RES, 'phase5e_gauge.json'), 'w'), indent=1)

# ------------------------------------------------------------------ H2 closure test: universal T3-surface subspace (FR30)
def fr30_vectors():
    """FR30 ground vectors at levels 4..7 (tile order of tiles_at_level; levels 5-7 from the D.geometry builder, validated identical)."""
    out = {}
    p4 = os.path.join(RES, 'phase5e_psi_fr30_L4.npy')
    if os.path.exists(p4): out[4] = np.load(p4)[:, 0]
    p5 = os.path.join(RES, 'phase5e_fr30_level7_L5_lowest4.npy')
    if os.path.exists(p5): out[5] = np.load(p5)[:, 0]
    p6 = os.path.join(RES, 'phase5b_e_fr30_level6_groundstate.npy')
    if os.path.exists(p6): out[6] = np.load(p6).ravel()
    p7 = os.path.join(RES, 'phase5e_fr30_level7_lowest4.npy')
    if os.path.exists(p7): out[7] = np.load(p7, mmap_mode='r')[:, 0]
    return out

def snapshots(psi, L, k, surf_k):
    """columns: restrictions of psi and T psi to the surface of every depth-(L-k) copy of T_k (local tile order)."""
    nk = 8 ** k; ncopy = 8 ** (L - k); loc = d.spinor(surf_k)
    idx = (np.arange(ncopy)[:, None] * (2 * nk) + loc[None, :])          # spinor index of copy j, local surface spinor q
    X = np.asarray(psi)[idx].T                                             # (2|surf|) x ncopy
    return np.c_[X, rg.kramers_partner(X)]

def run_closure(k=3):
    vecs = fr30_vectors(); tiles = d.tiles_of(FR30, k); _, edges = d.build(tiles); deg = d.degrees(len(tiles), edges); surf_k = np.nonzero(deg < 24)[0]
    out = {'k': k, 'surface_tiles': int(len(surf_k)), 'dim': int(2 * len(surf_k)), 'levels': sorted(vecs), 'per_level': {}}
    Xs = {}
    for L, v in vecs.items():
        v = np.asarray(v, complex); v = v / np.linalg.norm(v); X = snapshots(v, L, k, surf_k); Xs[L] = X / np.linalg.norm(X)
        sv = np.linalg.svd(Xs[L], compute_uv=False); e = sv ** 2 / (sv ** 2).sum(); tail = np.r_[np.clip(1 - np.cumsum(e), 0, None), np.zeros(600)]
        out['per_level'][L] = {'copies': int(8 ** (L - k)), 'surface_weight': float(np.linalg.norm(X) ** 2 / 2), 'tau_d': {str(dd): float(tail[dd - 1]) for dd in (2, 8, 16, 32, 57, 114, 287, 400, 500)},
                               'd_for_capture': {str(f): int(np.searchsorted(np.cumsum(e), f) + 1) for f in (0.9, 0.99, 0.999)}}
        log(f"[closure] L{L}: copies {8**(L-k)}, S-weight {out['per_level'][L]['surface_weight']:.4f}, d for 90/99/99.9% {out['per_level'][L]['d_for_capture']}, tau_57 {tail[56]:.4f}")
    def capture(U, X): return float(np.linalg.norm(U.conj().T @ X) ** 2 / np.linalg.norm(X) ** 2)
    out['transfer'] = {}
    for train in ([4], [4, 5], [4, 5, 6], [5], [6], [5, 6], [7], [6, 7]):     # [4]/[4,5] -> 6 pre-registered; the rest EXPLORATORY
        if not all(L in Xs for L in train): continue
        Xt = np.hstack([Xs[L] for L in train]); U, sv, _ = np.linalg.svd(Xt, full_matrices=False)
        for test in [L for L in sorted(Xs) if L not in train]:
            row = {str(dd): capture(U[:, :dd], Xs[test]) for dd in (8, 16, 20, 32, 41, 57, 114, 287)}
            out['transfer'][f"train{''.join(map(str, train))}_test{test}"] = row
            log(f"[closure] train {train} -> test L{test}: capture {row}")
    # the universal subspace used as the child basis at level 4 (children = T3 copies): compressed edge, out-of-level trained
    s4 = rg.System(FR30, 4); E0 = rg.ground_state(s4)[0][0]; out['level4_edge'] = {'E0': float(E0)}
    for train in ([5], [5, 6], [4], [6], [7], [6, 7]):
        if not all(L in Xs for L in train): continue
        U, _, _ = np.linalg.svd(np.hstack([Xs[L] for L in train]), full_matrices=False)
        for dd in (16, 20, 32, 41, 57, 114, 287):
            m = dd
            while m < U.shape[1] and m % 2: m += 1                     # keep Kramers pairs together (columns come in T-pairs)
            red = rg.Reduced(s4, [U[:, :m].copy() for _ in range(8)]); E, it = red.root()
            out['level4_edge'][f"train{''.join(map(str, train))}_d{m}"] = {'D': red.D, 'E_W': E, 'err': E - E0}
            log(f"[closure] universal U (train {train}, d={m}) at level 4: D={red.D} E_W-E0 = {E-E0:+.4f}")
    json.dump(out, open(os.path.join(RES, 'phase5e_closure.json'), 'w'), indent=1)

# ------------------------------------------------------------------ H1 operator locality (exploratory diagnostic)
def run_locality(names=('fr30', 1387, 3697, 2238), level=4):
    """Is the child response LOCAL across faces?  For every child c and every pair of its face/hinge/corner groups (A, B): the
    norm of R_c(E_REF)[A, B] relative to sqrt(||R_c[A, A]|| ||R_c[B, B]||), and its numerical rank at relative tolerance 1e-3
    (an H-matrix-type compressibility of the operator, as opposed to compressibility of the state)."""
    out = {}
    for nm in names:
        s = rg.System(spec_of(nm), level); rows = []
        for c in range(8):
            R = s.Rref(c); g = s.groups(c, 'face'); g.update(s.groups(c, 'hinge')); g.update(s.groups(c, 'corner')); labs = list(g)
            for i, A in enumerate(labs):
                for B in labs[i + 1:]:
                    a, b = d.spinor(g[A]), d.spinor(g[B]); blk = R[np.ix_(a, b)]
                    sv = np.linalg.svd(blk, compute_uv=False); na = np.linalg.norm(R[np.ix_(a, a)], 2); nb = np.linalg.norm(R[np.ix_(b, b)], 2)
                    rows.append({'child': c, 'A': str(A), 'B': str(B), 'rel_norm': float(sv[0] / np.sqrt(na * nb)) if len(sv) else 0.0,
                                 'rank_1e-3': int((sv > 1e-3 * sv[0]).sum()) if len(sv) and sv[0] > 0 else 0, 'shape': [len(a), len(b)]})
        rn = np.array([r['rel_norm'] for r in rows]); rk = np.array([r['rank_1e-3'] / min(r['shape']) for r in rows if min(r['shape']) > 0])
        out[str(nm)] = {'pairs': len(rows), 'rel_norm_median': float(np.median(rn)), 'rel_norm_max': float(rn.max()), 'rel_rank_median': float(np.median(rk)), 'rows': rows}
        log(f"[locality {nm}] {len(rows)} group pairs: off-diagonal relative norm median {np.median(rn):.2e} max {rn.max():.2e}; rank(1e-3)/min dim median {np.median(rk):.3f}")
    json.dump(out, open(os.path.join(RES, 'phase5e_locality.json'), 'w'), indent=1)

if __name__ == '__main__':
    cmd = sys.argv[1]
    if cmd == 'level4': run_level(4, int(sys.argv[2]), int(sys.argv[3]))
    elif cmd == 'level3': run_level(3, int(sys.argv[2]), int(sys.argv[3]))
    elif cmd == 'levels': run_levels(sys.argv[2])
    elif cmd == 'cluster':
        res = {nm: child_cluster(nm) for nm in sys.argv[2:]}; json.dump(res, open(os.path.join(RES, 'phase5e_cluster.json'), 'w'), indent=1)
    elif cmd == 'adaptive': run_adaptive(int(sys.argv[2]), int(sys.argv[3]))
    elif cmd == 'gauge': run_gauge()
    elif cmd == 'closure': run_closure()
    elif cmd == 'locality': run_locality()
    else: raise SystemExit(__doc__)
