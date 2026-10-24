#!/usr/bin/env python3
"""Phase X, Parts II-III (stage A): one evaluation record per gauge class of the 6561 proper Chair44 decorations.

Conventions (fixed for all of Phase X; deliverables/PHASE7_DEFINITIONS.md):
  * links U_f(a->b) = (sigma.M_a^T n_f)(sigma.M_b^T n_f) in Q8 (Pauli formula, phase9_pair.links);
  * pinned operator H_pin(K) = 24 - A_U on a finite tile set K (the compression of the hull operator, an UPPER bound on
    inf sigma for the hull of the rule when K is a legal patch);
  * free (Neumann) operator H_free(K) = Deg_K - A_U, Deg_K = panels of a tile inside K.  Every tiling of the hull of a rule
    is partitioned into level-k supertiles (geometric recognizability of the chair), each unitarily equivalent to T_k of
    the rule, and dropping the inter-supertile panel terms gives H_Y >= (+) H_free(T_k):  a LOWER bound on inf sigma;
  * volume convention: tiles; spinor dimension 2 per tile.
Gauge classes: S3-orbits (rigid axis permutations, phase9_pair.conj_dec) merged when verified gauge-equivalent
(audit/results/phase9_state.json).  The representative is the smallest decoration index in the class.

Record fields (per class): identity; Y_L = lambda_min H_pin(T_L) and F_k = lambda_min H_free(T_k) for L, k = 1..4;
plaquette and two-cycle conjugacy-class counts (level 3); exact closed-walk moments tr A^p/(2n), p = 2..8 (level 3);
radius-1 environments: the legal 1-star types (those of T_5, closed under Phi; complete when the frame substitution is primitive), U0 (pinned 1-star minimum), U1 (pinned sigma(tau) minimum),
mu0 (free 1-star minimum), the empirical frequency of the U1-minimising type, and the substitution graph Phi on 1-star
types (self-loops, spectral gap of the type-substitution matrix).  Census statistics of Phase V-B are attached by index.
Usage: python -u -I audit/phase10_census.py [nproc]  -> audit/results/phase10_census.jsonl (resumable), phase10_census.json"""
import os, sys, json, time, types, collections, itertools
sys.modules.setdefault('resource', types.SimpleNamespace(getrusage=lambda *a: types.SimpleNamespace(ru_maxrss=0), RUSAGE_SELF=0))
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); RES = os.path.join(HERE, 'results')
import numpy as np, scipy.sparse as sps, scipy.sparse.linalg as sla
import phase9_pair as P9
T0 = time.time()
def log(*a): print(f"[{time.time()-T0:7.0f}s]", *a, flush=True)
OUT = os.path.join(RES, 'phase10_census.jsonl')
# optional reuse of the level 1-4 eigenvalues, class counts and moments from an earlier run of this script (same code):
# set PHASE10_REUSE to the path of that run's phase10_census.json
REUSE = {r['class']: r for r in json.load(open(os.environ['PHASE10_REUSE']))['classes']} if os.environ.get('PHASE10_REUSE') else {}

def gauge_classes():
    """list of (representative, sorted members) for the 6561 proper decorations"""
    orbit = {}
    for i in range(3 ** 8):
        if i in orbit: continue
        orb = sorted({P9.index_of(P9.conj_dec(P9.decoration(i), Q)) for Q in P9.PERMS})
        for j in orb: orbit[j] = orb[0]
    st = json.load(open(os.path.join(RES, 'phase9_state.json'))); parent = {g: g for g in set(orbit.values())}
    for grp in st['isospectral_orbit_groups']:
        for h, eq in zip(grp['orbit_reps'][1:], grp['gauge_equivalent_to_first']):
            if eq: parent[h] = grp['orbit_reps'][0]
    cls = collections.defaultdict(list)
    for i, o in orbit.items(): cls[parent[o]].append(i)
    return sorted((min(m), sorted(m)) for m in cls.values())

def free_op(S):
    n = S['n']; deg = np.bincount(S['a'], minlength=n) + np.bincount(S['b'], minlength=n)
    return (S['H'] - sps.diags(np.repeat(24.0 - deg, 2))).tocsr()
def patch_ops(G, T):
    """pinned and free operators on an arbitrary tile set"""
    C = (np.einsum('nij,uj->nui', G, P9.BASE) + 2 * T[:, None, :] - 1) // 2; lo = C.reshape(-1, 3).min(0); C = C - lo
    grid = -np.ones(tuple(C.reshape(-1, 3).max(0) + 1), dtype=np.int64); grid[C[..., 0], C[..., 1], C[..., 2]] = np.arange(len(G))[:, None]
    a, b, ax = P9.panels(grid); n = len(G); Hp = P9.operator(G, a, b, ax, n)
    deg = np.bincount(a, minlength=n) + np.bincount(b, minlength=n)
    return Hp, (Hp - sps.diags(np.repeat(24.0 - deg, 2))).tocsr(), grid, lo
def lmin(H):
    if H.shape[0] <= 300: return float(np.linalg.eigvalsh(H.toarray())[0])
    return float(sla.eigsh(H, k=2, which='SA', tol=1e-10, ncv=40, return_eigenvectors=False).min())

def star_key(G, T, mem, t):
    Gt = G[t]; return tuple(sorted((tuple((Gt.T @ G[b]).ravel().tolist()), tuple((Gt.T @ (T[b] - T[t])).tolist())) for b in mem))
def stars_of(S):
    """complete 1-stars of a supertile: list of (tile, sorted member list)"""
    G, T, grid = S['G'], S['T'], S['grid']; N = grid.shape[0]
    C = (np.einsum('nij,oj->noi', G, 2 * P9.OFF1 + 1) + 2 * T[:, None, :] - 1) // 2
    inside = ((C >= 0) & (C < N)).all(-1).all(-1); out = []
    for t in np.nonzero(inside)[0]:
        own = grid[C[t, :, 0], C[t, :, 1], C[t, :, 2]]
        if (own >= 0).all(): out.append((int(t), sorted(set(own.tolist()))))
    return out

def record(rep_members):
    rep, members = rep_members; dec = P9.decoration(rep); r = {'class': rep, 'members': members, 'size': len(members),
                                                           'decoration': {str(k): list(v) for k, v in dec.items()}}
    t0 = time.time(); prev = REUSE.get(rep)
    if prev is not None:                                                      # identical code produced these fields in an earlier run
        for k in ('Y1', 'Y2', 'Y3', 'Y4', 'F1', 'F2', 'F3', 'F4', 'plaq_L3', 'twocyc_L3', 'moments_L3'): r[k] = prev[k]
    else:
        for L in (1, 2, 3, 4):
            S = P9.build([dec] * L); r[f'Y{L}'] = lmin(S['H']); r[f'F{L}'] = lmin(free_op(S))
            if L == 3:
                _, pc = P9.plaquettes(S); _, tc = P9.two_cycles(S); r['plaq_L3'] = P9.class_counts(pc); r['twocyc_L3'] = P9.class_counts(tc)
                tr, _ = P9.int_moments(S['H'], 8); r['moments_L3'] = [t / (2 * S['n']) for t in tr]
    S5 = P9.build([dec] * 5); stars = stars_of(S5); G5, T5 = S5['G'], S5['T']; types_ = {}; count = collections.Counter()
    for t, mem in stars:
        k = star_key(G5, T5, mem, t); count[k] += 1
        if k not in types_: types_[k] = (G5[mem], T5[mem], mem.index(t))
    n_t5 = len(types_)
    # Phi-closure: add the 1-stars of the children of the central tile, read inside sigma(tau), until nothing new appears.
    # With a primitive frame substitution the closure is the set of ALL legal 1-star types (Phase VII s.6.1); the level-5
    # supertile alone misses rare types.  The closure lemma guarantees every child 1-star is complete inside sigma(tau).
    keys = list(types_); index = {k: i for i, k in enumerate(keys)}; U0, U1, MU0, phi = [], [], [], []; i = 0
    while i < len(keys):
        G, T, c = types_[keys[i]]; Hp, Hf, _, _ = patch_ops(G, T); U0.append(lmin(Hp)); MU0.append(lmin(Hf))
        Gi, Ti = P9.inflate(G, T, dec); Hp1, _, grid, lo = patch_ops(Gi, Ti); U1.append(lmin(Hp1))
        ch = list(range(8 * c, 8 * c + 8)); N = np.array(grid.shape); img = []
        Cc = (np.einsum('nij,oj->noi', Gi[ch], 2 * P9.OFF1 + 1) + 2 * Ti[ch][:, None, :] - 1) // 2 - lo
        for j, tt in enumerate(ch):
            q = Cc[j]; assert ((q >= 0) & (q < N)).all(); own = grid[q[:, 0], q[:, 1], q[:, 2]]; assert (own >= 0).all(), 'closure lemma violated'
            mem = sorted(set(own.tolist())); kk = star_key(Gi, Ti, mem, tt)
            if kk not in index: index[kk] = len(keys); keys.append(kk); types_[kk] = (Gi[mem], Ti[mem], mem.index(tt))
            img.append(index[kk])
        phi.append(img); i += 1
    U0, U1, MU0 = np.array(U0), np.array(U1), np.array(MU0); amin = int(U1.argmin()); tot = sum(count.values())
    M = np.zeros((len(keys), len(keys)))
    for i, img in enumerate(phi):
        for j in img:
            if j >= 0: M[j, i] += 1
    ev = np.sort(np.abs(np.linalg.eigvals(M)))[::-1] if len(keys) > 1 else np.array([8.0, 0.0])
    r.update({'n_types1': len(keys), 'n_types1_in_T5': n_t5, 'U0': float(U0.min()), 'U1': float(U1.min()), 'mu0': float(MU0.min()), 'mu0_max': float(MU0.max()),
              'U1_argmin_frequency': count[keys[amin]] / tot, 'U1_second': float(np.sort(U1)[1]) if len(U1) > 1 else None,
              'phi_complete': bool(all(j >= 0 for img in phi for j in img)), 'phi_self_loops': int(sum(1 for i, img in enumerate(phi) if i in img)),
              'phi_perron': float(ev[0]), 'phi_second': float(ev[1]), 'seconds': time.time() - t0})
    return r

def merge():
    """one record per class (the last written wins; the 7 classes written twice by an overlapping run agree to 4e-13), with the
    Phase V-B statistics attached -> phase10_census.json"""
    recs = sorted({json.loads(l)['class']: json.loads(l) for l in open(OUT)}.values(), key=lambda r: r['class'])
    sw = {r['index']: r for r in json.load(open(os.path.join(RES, 'phase5b_sweep.json')))['records']}
    for r in recs: r['census_pred_L4'] = {k: v for k, v in sw[r['class']]['pred'].items() if isinstance(v, (int, float))}
    json.dump({'conventions': __doc__, 'classes': recs}, open(os.path.join(RES, 'phase10_census.json'), 'w'), default=float)
    log(f"wrote {len(recs)} records")

if __name__ == '__main__':
    import multiprocessing as mp
    if sys.argv[1:] == ['merge']: merge(); sys.exit()
    nproc = int(sys.argv[1]) if len(sys.argv) > 1 else 12
    classes = gauge_classes(); log(f"{len(classes)} gauge classes, sizes {collections.Counter(len(m) for _, m in classes)}")
    done = set()
    if os.path.exists(OUT):
        for l in open(OUT): done.add(json.loads(l)['class'])
    todo = [c for c in classes if c[0] not in done]; log(f"{len(done)} done, {len(todo)} to do")
    with mp.Pool(nproc) as pool, open(OUT, 'a') as f:
        for i, r in enumerate(pool.imap_unordered(record, todo, chunksize=1)):
            f.write(json.dumps(r) + '\n'); f.flush()
            if i % 50 == 0: log(f"{i + 1}/{len(todo)} class {r['class']}: Y3 {r['Y3']:.4f} Y4 {r['Y4']:.4f} F4 {r['F4']:.4f} U1 {r['U1']:.4f} types {r['n_types1']}")
    merge()
