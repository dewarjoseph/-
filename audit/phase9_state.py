#!/usr/bin/env python3
"""Phase IX, Part IV: which summary of a Chair44 decoration predicts its spectral bottom on unseen decorations?

Data: the complete census of the 3^8 = 6561 proper decorations (audit/results/phase5b_sweep.json, Phase V-B): Y3 for all of
them, Y4 for the preregistered sample of 401, and 45 level-4 plaquette statistics.  New here:
  * S3-orbits (rigid axis permutations, phase9_pair.conj_dec).  Decorations in one orbit are isospectral and have identical
    gauge-invariant statistics, so every held-out evaluation below holds out WHOLE ORBITS (grouped cross-validation).  The
    V-B analysis used ungrouped 10-fold cross-validation, in which copies of a test decoration sit in the training folds.
  * local spectral summaries computed here for every decoration: Y1, Y2 (pinned level-1/2 supertiles), the 4 softest
    eigenvalues of the level-2 surface response R_2(E0) at E0 = 6 (gauge-invariant, Kramers pairs).
Candidate summaries (nested where possible):
  counts        f_m1, f_trl                                   (plaquette conjugacy-class fractions; the V-B flux model)
  loops         counts + 2x1 and 2x2 Wilson-loop class fractions
  correlations  loops + plaquette class-pair correlations, -1 clustering, per-tile spread, depth enrichments (all 41 SU(2)-invariant)
  local_Y       Y1, Y2
  response      the 4 softest eigenvalues of R_2(E0)
  local_Y+counts, response+counts
Tests: (1) exact sufficiency on the census: two orbits with equal summaries (to 1e-9) but different Y3 is a counterexample;
(2) grouped 10-fold CV-RMSE of OLS and of k-nearest-neighbour regression (two model classes), targets Y3 and Y4;
(3) FR30 held out entirely: its predicted Y3, Y4 from each summary trained on all other orbits.
Grouping: S3-orbits merged when isospectral at level 3 and verified gauge-equivalent (tree gauge, binary octahedral conjugation).
Usage: python -u -I audit/phase9_state.py -> audit/results/phase9_state.json
       python -u -I audit/phase9_state.py closure -> audit/results/phase9_count_closure.json"""
import os, sys, json, time, collections, types
sys.modules.setdefault('resource', types.SimpleNamespace(getrusage=lambda *a: types.SimpleNamespace(ru_maxrss=0), RUSAGE_SELF=0))
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); RES = os.path.join(HERE, 'results')
import numpy as np
import phase9_pair as P9
T0 = time.time()
def log(*a): print(f"[{time.time()-T0:7.0f}s]", *a, flush=True)
FOLD_SEED = 20261023; E0 = 6.0

def local_features(i):
    """Y1, Y2 and the 4 softest eigenvalues of R_2(E0) for decoration i"""
    dec = P9.decoration(i); out = {}
    for L in (1, 2):
        S = P9.build([dec] * L); H = S['H'].toarray(); out[f'Y{L}'] = float(np.linalg.eigvalsh(H)[0])
    S = P9.build([dec] * 2); grid = S['grid']; n = S['n']; deg = np.bincount(S['a'], minlength=n) + np.bincount(S['b'], minlength=n)
    surf = np.nonzero(deg < 24)[0]; inte = np.nonzero(deg == 24)[0]; sp = lambda x: np.ravel(np.c_[2 * x, 2 * x + 1])
    H = S['H'].toarray(); ss, ii = sp(surf), sp(inte)
    R = H[np.ix_(ss, ss)] - E0 * np.eye(len(ss)) - H[np.ix_(ss, ii)] @ np.linalg.solve(H[np.ix_(ii, ii)] - E0 * np.eye(len(ii)), H[np.ix_(ii, ss)])
    w = np.linalg.eigvalsh(R); out['R2'] = w[:8:2].tolist()                               # Kramers pairs: every other value
    return out

def tree_key(S):
    """holonomies of the fundamental cycles of a BFS spanning tree from tile 0 (tree gauge); two decorations on the same
    (cube-matched) tiles define gauge-equivalent connections iff these agree up to one global conjugation (definitions s.3)"""
    n = S['n']; a, b = S['a'], S['b']; U = P9.links(S['G'], a, b, S['ax']); adj = collections.defaultdict(list)
    for e, (x, y) in enumerate(zip(a.tolist(), b.tolist())): adj[x].append((y, e, False)); adj[y].append((x, e, True))
    g = [None] * n; g[0] = np.eye(2, dtype=complex); q = collections.deque([0]); tree = set()
    while q:
        x = q.popleft()
        for y, e, rev in adj[x]:
            if g[y] is None: g[y] = g[x] @ (U[e].conj().T if rev else U[e]); tree.add(e); q.append(y)
    return np.array([g[a[e]] @ U[e] @ g[b[e]].conj().T for e in range(len(a)) if e not in tree])
def octahedral():
    I = np.eye(2); X, Y, Z = P9.SIG; s = 1 / np.sqrt(2)
    q8 = [sg * m for m in (I, -1j * X, -1j * Y, -1j * Z) for sg in (1, -1)]
    tet = [0.5 * (I * a - 1j * (b * X + c * Y + d * Z)) for a in (1, -1) for b in (1, -1) for c in (1, -1) for d in (1, -1)]
    return q8 + tet + [g @ (s * (I - 1j * X)) for g in q8 + tet]
def gauge_equivalent(i, j, L=3):
    A = P9.build([P9.decoration(i)] * L); B = P9.build([P9.decoration(j)] * L, ref=A['grid']); W1, W2 = tree_key(A), tree_key(B)
    return any(np.allclose(np.einsum('ij,njk,kl->nil', h, W1, h.conj().T), W2, atol=1e-9) for h in octahedral())

def grouped_cv(X, y, groups, model, k=10):
    ug = np.unique(groups); rng = np.random.default_rng(FOLD_SEED); perm = rng.permutation(len(ug)); fold_of = {g: f % k for f, g in zip(range(len(ug)), ug[perm])}
    f = np.array([fold_of[g] for g in groups]); pred = np.zeros(len(y))
    for j in range(k):
        tr, te = f != j, f == j; pred[te] = model(X[tr], y[tr], X[te])
    return pred
def ols(Xtr, ytr, Xte):
    mu, sd = Xtr.mean(0), Xtr.std(0) + 1e-12; A = np.c_[np.ones(len(Xtr)), (Xtr - mu) / sd]; c, *_ = np.linalg.lstsq(A, ytr, rcond=None)
    return np.c_[np.ones(len(Xte)), (Xte - mu) / sd] @ c
def knn(Xtr, ytr, Xte, kk=5):
    mu, sd = Xtr.mean(0), Xtr.std(0) + 1e-12; A, B = (Xtr - mu) / sd, (Xte - mu) / sd
    d = ((B[:, None, :] - A[None, :, :]) ** 2).sum(-1); idx = np.argsort(d, 1)[:, :kk]; return ytr[idx].mean(1)

def main():
    D = json.load(open(os.path.join(RES, 'phase5b_sweep.json'))); R = sorted(D['records'], key=lambda r: r['index']); fr = D['fr30_index']
    idx = np.array([r['index'] for r in R]); Y3 = np.array([r['L3']['lambda'][0] for r in R])
    Y4 = np.array([r['L4']['lambda'][0] if r.get('L4') else np.nan for r in R])
    orbit = {}
    for i in idx.tolist():
        if i in orbit: continue
        orb = sorted({P9.index_of(P9.conj_dec(P9.decoration(i), Q)) for Q in P9.PERMS})
        for j in orb: orbit[j] = orb[0]
    groups = np.array([orbit[i] for i in idx.tolist()]); out = {'decorations': len(idx), 'orbits': int(len(np.unique(groups)))}
    spread = max(np.ptp(Y3[groups == g]) for g in np.unique(groups)); out['max_Y3_spread_within_orbit'] = float(spread)
    log(f"{len(idx)} decorations, {out['orbits']} S3-orbits; max Y3 spread inside an orbit {spread:.2e}")
    # merge orbits that are isospectral at level 3 AND verified gauge-equivalent (tree-gauge holonomies up to global conjugation)
    by = collections.defaultdict(list)
    for g in np.unique(groups): by[round(float(Y3[groups == g][0]), 8)].append(int(g))
    merged, iso = {int(g): int(g) for g in np.unique(groups)}, []; orbit_rep_all = groups.copy()
    for v, gs in by.items():
        if len(gs) < 2: continue
        members = {h: sorted(int(i) for i in idx[orbit_rep_all == h]) for h in gs}
        eq = [any(gauge_equivalent(gs[0], m) for m in members[h]) for h in gs[1:]]; iso.append({'Y3': v, 'orbit_reps': gs, 'gauge_equivalent_to_first': eq})
        for h, e in zip(gs[1:], eq):
            if e: merged[h] = gs[0]
    orbit_rep = groups.copy(); groups = np.array([merged[int(g)] for g in groups])
    out['isospectral_orbit_groups'] = iso; out['gauge_classes'] = int(len(np.unique(groups)))
    out['isospectral_but_not_gauge_equivalent'] = sum(1 for r in iso for e in r['gauge_equivalent_to_first'] if not e)
    log(f"{len(iso)} sets of isospectral orbits; gauge classes {out['gauge_classes']}; isospectral but inequivalent: {out['isospectral_but_not_gauge_equivalent']}")
    # local spectral features for one representative per orbit (orbit members are isospectral; verified on a sample below)
    cache = os.path.join(RES, 'phase9_local_features.json')
    feats = json.load(open(cache)) if os.path.exists(cache) else {}
    reps = sorted(set(orbit_rep.tolist()))
    for c, g in enumerate(reps):
        if str(g) not in feats: feats[str(g)] = local_features(g)
        if c % 200 == 0: log(f"local features {c}/{len(reps)}")
    json.dump(feats, open(cache, 'w'))
    chk = [i for i in idx.tolist()[:: 97]]; dev = max(abs(local_features(i)['Y2'] - feats[str(orbit[i])]['Y2']) for i in chk); out['orbit_isospectral_check_Y2'] = float(dev)
    pred = [r['pred'] for r in R]; names = [k for k, v in pred[0].items() if isinstance(v, (int, float)) and not isinstance(v, bool)]
    axis = {'n_i', 'n_j', 'n_k', 'f_i', 'f_j', 'f_k'}; extensive = {'N_inter', 'n_plus', 'n_minus', 'n_traceless', 'n_panel_pairs'}
    loopn = ['loop21_f_m1', 'loop21_f_trl', 'loop22_f_m1', 'loop22_f_trl']
    corr = [k for k in names if k not in axis | extensive | {'f_m1', 'f_trl', 'f_nontriv'} | set(loopn) and not k.startswith('strad')]
    col = lambda ks: np.array([[p[k] for k in ks] for p in pred], float)
    F = {g_: feats[str(g_)] for g_ in reps}
    local = np.array([[F[g]['Y1'], F[g]['Y2']] for g in orbit_rep]); resp = np.array([F[g]['R2'] for g in orbit_rep])
    sets = {'counts': col(['f_m1', 'f_trl']), 'loops': col(['f_m1', 'f_trl'] + loopn), 'correlations': col(['f_m1', 'f_trl'] + loopn + corr),
            'local_Y': local, 'response': resp, 'local_Y+counts': np.c_[local, col(['f_m1', 'f_trl'])], 'response+counts': np.c_[resp, col(['f_m1', 'f_trl'])]}
    out['feature_names'] = {'counts': ['f_m1', 'f_trl'], 'loops': loopn, 'correlations_extra': corr, 'local_Y': ['Y1', 'Y2'], 'response': [f'R2(E0={E0}) pair {k}' for k in range(4)]}
    res = {}
    for name, X in sets.items():
        row = {}
        # exact sufficiency on the census: equal summaries, different Y3
        key = collections.defaultdict(set)
        for x, y, g in zip(np.round(X, 9).tolist(), Y3.tolist(), groups.tolist()): key[tuple(x)].add((g, round(y, 7)))
        clash = [sorted(v) for v in key.values() if len({y for _, y in v}) > 1]
        row['distinct_summaries'] = len(key); row['collisions_with_different_Y3'] = len(clash); row['example_collision'] = clash[0][:4] if clash else None
        for tname, y in (('Y3', Y3), ('Y4', Y4)):
            m = np.isfinite(y) & (idx != fr)
            for mname, model in (('ols', ols), ('knn', knn)):
                p = grouped_cv(X[m], y[m], groups[m], model); e = p - y[m]
                row[f'{tname}_{mname}_cv_rmse'] = float(np.sqrt(np.mean(e ** 2))); row[f'{tname}_{mname}_cv_r2'] = float(1 - np.mean(e ** 2) / np.var(y[m]))
                # FR30 held out entirely: train on every other orbit
                tr = m & (groups != orbit[fr]); fx = X[idx == fr]
                row[f'{tname}_{mname}_fr30_pred'] = float(model(X[tr], y[tr], fx)[0]); row[f'{tname}_fr30_true'] = float(y[idx == fr][0])
        res[name] = row; log(name, {k: (round(v, 4) if isinstance(v, float) else v) for k, v in row.items() if k != 'example_collision'})
    out['results'] = res; out['n_Y4'] = int(np.isfinite(Y4).sum()); out['Y3_sd'] = float(Y3.std()); out['Y4_sd'] = float(np.nanstd(Y4))
    # renormalization closure of the summaries across levels: is the level-(m+1) value a function of the level-m value?
    clo = {}
    for a, b in (('Y1', 'Y2'), ('Y2', 'Y3')):
        va = np.array([F[g][a] for g in reps]); vb = np.array([F[g][b] for g in reps]) if b != 'Y3' else np.array([Y3[orbit_rep == g][0] for g in reps])
        kk = collections.defaultdict(set)
        for x, y in zip(np.round(va, 9), np.round(vb, 7)): kk[x].add(y)
        clo[f'{a}->{b}'] = {'distinct_inputs': len(kk), 'inputs_with_several_outputs': sum(len(v) > 1 for v in kk.values())}
    out['closure'] = clo; log('closure', clo)
    json.dump(out, open(os.path.join(RES, 'phase9_state.json'), 'w'), indent=1, default=float)

def count_closure():
    """renormalization closure of plaquette class counts on the census: is the level-4 count vector (n+, n-, sorted axis counts)
    a function of the level-3 one across the S3-orbits?  -> audit/results/phase9_count_closure.json"""
    D = json.load(open(os.path.join(RES, 'phase5b_sweep.json'))); R = {r['index']: r for r in D['records']}; orbit = {}
    for i in sorted(R):
        if i in orbit: continue
        orb = sorted({P9.index_of(P9.conj_dec(P9.decoration(i), Q)) for Q in P9.PERMS})
        for j in orb: orbit[j] = orb[0]
    reps = sorted(set(orbit.values())); c3, c4 = {}, {}
    for g in reps:
        _, cls = P9.plaquettes(P9.build([P9.decoration(g)] * 3)); c = P9.class_counts(cls)
        c3[g] = (c['+1'], c['-1'], tuple(sorted((c['i'], c['j'], c['k'])))); p = R[g]['pred']
        c4[g] = (p['n_plus'], p['n_minus'], tuple(sorted((p['n_i'], p['n_j'], p['n_k']))))
    m, y3 = collections.defaultdict(set), collections.defaultdict(set)
    for g in reps: m[c3[g]].add(c4[g]); y3[c3[g]].add(round(R[g]['L3']['lambda'][0], 7))
    multi = [(k, v) for k, v in m.items() if len(v) > 1]
    out = {'orbits': len(reps), 'distinct_L3_count_vectors': len(m), 'L3_vectors_with_several_L4_vectors': len(multi),
           'examples': [[list(k), [list(x) for x in v]] for k, v in multi[:5]], 'L3_count_vectors_with_different_Y3': sum(len(v) > 1 for v in y3.values())}
    log('count closure', out); json.dump(out, open(os.path.join(RES, 'phase9_count_closure.json'), 'w'), indent=1, default=list)

if __name__ == '__main__':
    if sys.argv[1:] == ['closure']: count_closure()
    else: main()
