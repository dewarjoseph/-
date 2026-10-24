#!/usr/bin/env python3
"""Phase X, Part III stage B: deep confirmation of the screened candidates (rules fixed in phase10_preregistration.json).

  select   apply the pre-registered selection to phase10_census.json -> phase10_stageB_selection.json
           (15 largest Y4, then 5 largest F4 not yet chosen, plus the FR30, 937 and 938 classes; and the random sample of
            200 classes for the Part V deeper-level target, numpy default_rng(20261024))
  y5       Y5 (pinned level 5, residual) for every selected and sampled class; exact Rayleigh upper certificate of Y5 for the
           selected ones -> phase10_y5.jsonl (resumable; F5 only in the records of the first run, see y5_job)
  deep_one <class>   one process per class (deep_targets prints them): for the 5 selected classes with the largest Y5 (the
           pre-declared second stage) plus FR30, Y6 with residual and its exact Rayleigh upper certificate, the
           certified level-4 enclosure, independent reconstruction at level 3 through the census builder, the chain bounds
           U2 (all legal 1-star types: the Phi-closure) and U3 (20 lowest U2) -> phase10_deep.jsonl
  promote  the registered promotion checks and the last-ratio finite-size baseline -> phase10_stageB_promotion.json
  upper6 <class>   an additional certified upper bound (exact Rayleigh quotient at level 6) -> phase10_upper6.jsonl
Usage: python -u -I audit/phase10_stageB.py <cmd> [nproc]"""
import os, sys, json, time, math, types, collections
from fractions import Fraction
sys.modules.setdefault('resource', types.SimpleNamespace(getrusage=lambda *a: types.SimpleNamespace(ru_maxrss=0), RUSAGE_SELF=0))
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); RES = os.path.join(HERE, 'results')
import numpy as np, scipy.sparse as sps, scipy.sparse.linalg as sla
import phase9_pair as P9
import phase10_census as C
T0 = time.time()
def log(*a): print(f"[{time.time()-T0:7.0f}s]", *a, flush=True)
FR30_CLASS, C937, C938 = 1386, 937, 938

def load_census(): return {r['class']: r for r in json.load(open(os.path.join(RES, 'phase10_census.json')))['classes']}

def cmd_select():
    cen = load_census(); pre = json.load(open(os.path.join(RES, 'phase10_preregistration.json')))
    by_y4 = sorted(cen, key=lambda c: -cen[c]['Y4']); chosen = by_y4[:15]
    for c in sorted(cen, key=lambda c: -cen[c]['F4']):
        if len(chosen) >= 20: break
        if c not in chosen: chosen.append(c)
    bench = [FR30_CLASS, C937, C938]; sample = sorted(int(x) for x in np.random.default_rng(20261024).choice(sorted(cen), size=200, replace=False))
    out = {'rule': pre['stage_B_selection']['rule'], 'selected': chosen, 'benchmarks': bench, 'random_sample_200': sample,
           'selected_rows': [{k: cen[c][k] for k in ('class', 'members', 'Y3', 'Y4', 'F4', 'U1', 'n_types1')} for c in chosen]}
    json.dump(out, open(os.path.join(RES, 'phase10_stageB_selection.json'), 'w'), indent=1); log('selected', chosen)

def exact_rayleigh(H, v):
    v = v / np.abs(v).max(); s = 2 ** 20; xr = np.rint(v.real * s).astype(np.int64); xi = np.rint(v.imag * s).astype(np.int64)
    Re = H.real.tocsr(); Im = H.imag.tocsr(); assert np.array_equal(Re.data, np.rint(Re.data)) and np.array_equal(Im.data, np.rint(Im.data))
    Re = Re.astype(np.int64); Im = Im.astype(np.int64); yr = Re @ xr - Im @ xi; yi = Re @ xi + Im @ xr
    num = int(np.dot(xr.astype(object), yr.astype(object))) + int(np.dot(xi.astype(object), yi.astype(object)))
    den = int(np.dot(xr.astype(object), xr.astype(object))) + int(np.dot(xi.astype(object), xi.astype(object)))
    return Fraction(num, den)

def eig_res(H, ncv=48, tol=1e-11):
    w, V = sla.eigsh(H, k=2, which='SA', tol=tol, ncv=ncv); i = int(np.argmin(w)); v = V[:, i]
    return float(w[i]), float(np.linalg.norm(H @ v - w[i] * v)), v

def y5_job(args):
    """selected classes: Y5 (tol 1e-10) and the exact Rayleigh certificate; sample classes: Y5 only (tol 1e-9).  (F5 was computed
    for the first classes only: the free level-5 eigensolve converges slowly on its clustered surface states, and the matched-volume
    free-versus-pinned comparison uses level 4, Y4 versus F4, available for every class.)"""
    cls, certify = args; dec = P9.decoration(cls); S = P9.build([dec] * 5); lam, res, v = eig_res(S['H'], tol=1e-10 if certify else 1e-9)
    rec = {'class': cls, 'Y5': lam, 'Y5_residual': res}
    if certify:
        q = exact_rayleigh(S['H'], v); rec.update({'Y5_upper_exact': f'{q.numerator}/{q.denominator}', 'Y5_upper': float(q)})
    return rec

def cmd_y5(nproc=8):
    import multiprocessing as mp
    sel = json.load(open(os.path.join(RES, 'phase10_stageB_selection.json'))); out = os.path.join(RES, 'phase10_y5.jsonl')
    cert = set(sel['selected']) | set(sel['benchmarks']); allc = sorted(cert | set(sel['random_sample_200']))
    done = {json.loads(l)['class'] for l in open(out)} if os.path.exists(out) else set()
    todo = [(c, c in cert) for c in allc if c not in done]; log(f"Y5: {len(todo)} classes to do")
    with mp.Pool(nproc) as pool, open(out, 'a') as f:
        for i, r in enumerate(pool.imap_unordered(y5_job, todo)):
            f.write(json.dumps(r) + '\n'); f.flush()
            if i % 20 == 0: log(f"{i + 1}/{len(todo)} class {r['class']}: Y5 {r['Y5']:.6f} (res {r['Y5_residual']:.1e}) F5 {r.get('F5')}")

def deep_targets():
    """the 5 selected classes with the largest Y5.  A class whose Y5 is not yet computed can be left out only if its Y4 is below
    the fifth-largest computed Y5, since Y5 <= Y4 (interlacing: T4 embeds in T5 with the same links)"""
    sel = json.load(open(os.path.join(RES, 'phase10_stageB_selection.json'))); y5 = {json.loads(l)['class']: json.loads(l) for l in open(os.path.join(RES, 'phase10_y5.jsonl'))}
    have = sorted((c for c in sel['selected'] if c in y5), key=lambda c: -y5[c]['Y5']); cen = load_census()
    fifth = y5[have[4]]['Y5'] if len(have) >= 5 else float('inf')
    missing = [c for c in sel['selected'] if c not in y5 and cen[c]['Y4'] >= fifth]; assert not missing, f'Y5 missing for {missing}'
    return have[:5]

def cmd_deep_targets():
    print(' '.join(str(c) for c in deep_targets() + [FR30_CLASS]))

def cmd_deep_one(cls):
    """the second-stage computations for one class (run one process per class)"""
    top5 = deep_targets(); assert cls in top5 + [FR30_CLASS]
    dec = P9.decoration(cls); rec = {'class': cls, 'top5_by_Y5': cls in top5}; t0 = time.time()
    from independent_clifford_q8_audit import panel_edges
    from phase5a_controls import clifford_links, build_H
    from phase5b_controls import system_tiles
    tiles, _ = system_tiles(f'dec{cls}', 3); n = len(tiles); _, ed = panel_edges(tiles)
    e_census = np.linalg.eigvalsh(build_H(n, ed, clifford_links(tiles, ed), np.full(n, 24.0)).toarray())
    e_ours = np.linalg.eigvalsh(P9.build([dec] * 3)['H'].toarray()); rec['reconstruction_L3_max_spectral_difference'] = float(np.abs(e_census - e_ours).max())
    S4 = P9.build([dec] * 4); y4 = P9.lam_min(S4['H']); q = P9.rayleigh_upper(S4['H']); mu = Fraction(math.floor((y4 - 1e-6) * 2 ** 20), 2 ** 20)
    import phase10_ims as I
    rec['Y4_certified'] = [I.cert_lower_sparse(S4['H'], mu), float(q)]; log(cls, 'certified L4', rec['Y4_certified'])
    types_, n5 = I.phi_closed_types(dec); U2, pats = [], []                     # all legal 1-star types (Phi-closure)
    for G, T, _ in types_.values():
        for _ in range(2): G, T = P9.inflate(G, T, dec)
        U2.append(P9.lam_min_sparse(P9.patch_H(G, T))); pats.append((G, T))
    U2 = np.array(U2); U3 = []
    for i in np.argsort(U2)[:20]:
        G, T = P9.inflate(*pats[i], dec); U3.append(P9.lam_min_sparse(P9.patch_H(G, T)))
    rec.update({'U2': float(U2.min()), 'U3_top20': float(min(U3)), 'n_types1': len(types_), 'n_types1_T5': n5}); log(cls, 'chain', rec['U2'], rec['U3_top20'])
    del pats
    S6 = P9.build([dec] * 6); lam6, res6, v6 = eig_res(S6['H'], ncv=40, tol=1e-10); q6 = exact_rayleigh(S6['H'], v6)
    rec.update({'Y6': lam6, 'Y6_residual': res6, 'Y6_upper_exact': f'{q6.numerator}/{q6.denominator}', 'Y6_upper': float(q6), 'seconds': time.time() - t0})
    log(rec)
    with open(os.path.join(RES, 'phase10_deep.jsonl'), 'a') as f: f.write(json.dumps(rec) + '\n')

def cmd_upper6(cls):
    """an additional certified upper bound on E_* (a certification step, not a selection step): the exact rational Rayleigh
    quotient of the level-6 ground vector -> phase10_upper6.jsonl"""
    S6 = P9.build([P9.decoration(cls)] * 6); lam, res, v = eig_res(S6['H'], ncv=40, tol=1e-10); q = exact_rayleigh(S6['H'], v)
    rec = {'class': cls, 'Y6': lam, 'Y6_residual': res, 'Y6_upper_exact': f'{q.numerator}/{q.denominator}', 'Y6_upper': float(q)}; log(rec)
    with open(os.path.join(RES, 'phase10_upper6.jsonl'), 'a') as f: f.write(json.dumps(rec) + '\n')

def cmd_promote():
    """the registered promotion test for the deep-stage classes -> phase10_stageB_promotion.json.  Finite-size baseline: the
    last-ratio (geometric-tail) extrapolation from Y4, Y5, Y6, an estimate only [X]; a candidate survives it when its baseline
    exceeds FR30's (the finite-level ordering is not reversed by the extrapolation)."""
    cen = load_census(); y5 = {json.loads(l)['class']: json.loads(l) for l in open(os.path.join(RES, 'phase10_y5.jsonl'))}
    deep = {json.loads(l)['class']: json.loads(l) for l in open(os.path.join(RES, 'phase10_deep.jsonl'))}
    def baseline(Y):
        d1, d2 = Y[-3] - Y[-2], Y[-2] - Y[-1]; q = d2 / d1; return Y[-1] - d2 * q / (1 - q), q
    rows = {}
    for c, d in deep.items():
        Y = [cen[c]['Y3'], cen[c]['Y4'], y5[c]['Y5'], d['Y6']]; b, q = baseline(Y[1:]); lo4, up4 = d['Y4_certified']
        rows[c] = {'class': c, 'Y3..Y6': Y, 'last_ratio': q, 'baseline_estimate': b, 'Y5_upper_certified': y5[c].get('Y5_upper'), 'F5': y5[c].get('F5'),
                   'checks': {'independent_reconstruction_L3': d['reconstruction_L3_max_spectral_difference'] < 1e-9,
                              'residual_Y6_below_1e-8': d['Y6_residual'] < 1e-8, 'residual_Y5_below_1e-8': y5[c]['Y5_residual'] < 1e-8,
                              'certified_L4_enclosure': lo4 is not None and lo4 <= cen[c]['Y4'] <= up4 + 1e-12,
                              'free_below_pinned_matched_volume_L5': y5[c].get('F5') is not None and y5[c]['F5'] <= y5[c]['Y5'],
                              'monotone_convergent_levels': all(a > b_ for a, b_ in zip(Y, Y[1:])) and 0 < q < 1}}
    fr = rows.get(FR30_CLASS)
    for c, r in rows.items():
        r['checks']['baseline_above_FR30'] = None if c == FR30_CLASS or fr is None else r['baseline_estimate'] > fr['baseline_estimate']
        r['promoted'] = c != FR30_CLASS and all(v for v in r['checks'].values())
    json.dump({'rule': 'promotion requires every check (phase10_preregistration.json stage_B_selection.promotion)', 'rows': list(rows.values())},
              open(os.path.join(RES, 'phase10_stageB_promotion.json'), 'w'), indent=1)
    for r in rows.values(): log(r['class'], 'promoted' if r['promoted'] else 'not promoted', {k: v for k, v in r['checks'].items() if not v})

if __name__ == '__main__':
    cmd = sys.argv[1]; arg = sys.argv[2:]
    globals()[f'cmd_{cmd}'](*[int(a) for a in arg])
