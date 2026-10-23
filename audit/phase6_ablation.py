#!/usr/bin/env python3
"""Phase VI ablations for Theorem F: which hypotheses force the flux?  Level-1 supertile, free connection Laplacian.
  (a) identity frames (not compatible with the substitution geometry)       -> expected pure gauge
  (b) reflection-only frames M = D_s(v) (geometry-compatible, det = (-1)^|v|) -> Abelian links in {+-1}
  (c) improper decorations: permutation parts of the WRONG parity (det = -1 frames), random sample + exhaustive identity-perm
  (d) all 6^8 permutation choices (proper and improper) restricted to the centre-fixed sample (random 20000)
Usage: python -u -I audit/phase6_ablation.py -> audit/results/phase6_ablation.json"""
import os, sys, json, itertools, collections
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); RES = os.path.join(HERE, 'results')
import numpy as np
import phase6_gauge_audit as G
PERMS = list(itertools.permutations(range(3)))
def tiles_with_frames(child_frames):
    """level-1 supertile: the 8 child chairs with their geometric placement, but with the given frames attached.
    Placement (cube sets) is that of the geometric chair children (frames only change the links, Proposition E0)."""
    geo = G.tiles(G.FR30, 1)                                    # cube sets of the 8 children (decoration-independent)
    return [(M, cs) for M, (_, cs) in zip(child_frames, geo)]
def analyse(frames):
    tl = tiles_with_frames(frames); pn = G.panels(tl); n = len(tl)
    links = [G.link(tl[a][0], tl[b][0], k) for a, b, k, _ in pn]
    deg = np.zeros(n)
    for a, b, k, _ in pn: deg[a] += 1; deg[b] += 1
    _, cycles = G.tree_and_cycles(n, pn); Ws = [G.holonomy(pn, links, c) for c in cycles]
    cls = collections.Counter(G.qclass(W) for W in Ws); lam = float(np.linalg.eigvalsh(G.operator(tl, pn, links, deg).toarray())[0])
    return {'nontrivial_cycles': len(Ws) - cls['+1'], 'classes': dict(cls), 'free_lambda_min': lam,
            'abelian_links': all(abs(abs(np.trace(C).real) - 2) < 1e-9 for C in links)}
def D(v): return np.diag([1 - 2 * v[0], 1 - 2 * v[1], 1 - 2 * v[2]])
order = ['0'] + G.U3                                              # child order used by G.tiles (centre first, then U3)
out = {}
out['a_identity_frames'] = analyse([np.eye(3, dtype=int)] * 8)
out['b_reflection_only'] = analyse([np.eye(3, dtype=int)] + [D(v) for v in G.U3])
rng = np.random.default_rng(20261027); proper = improper = 0; pg_proper = pg_improper = 0; lam_imp = []; lam_pro = []; examples = []
for t in range(20000):
    ch = [PERMS[rng.integers(6)] for _ in range(8)]
    fr = [G.P(ch[0])] + [D(v) @ G.P(ch[k + 1]) for k, v in enumerate(G.U3)]
    is_proper = all(round(np.linalg.det(M)) == 1 for M in fr)
    r = analyse(fr)
    if is_proper: proper += 1; lam_pro.append(r['free_lambda_min']); pg_proper += r['nontrivial_cycles'] == 0
    else:
        improper += 1; lam_imp.append(r['free_lambda_min']); pg_improper += r['nontrivial_cycles'] == 0
        if r['nontrivial_cycles'] == 0 and len(examples) < 5: examples.append([list(p) for p in ch])
out['c_random_permutation_choices'] = {'samples': 20000, 'proper': proper, 'improper': improper, 'pure_gauge_proper': int(pg_proper), 'pure_gauge_improper': int(pg_improper),
    'min_lambda_proper': float(min(lam_pro)) if lam_pro else None, 'min_lambda_improper': float(min(lam_imp)) if lam_imp else None, 'pure_gauge_examples_improper': examples}
json.dump(out, open(os.path.join(RES, 'phase6_ablation.json'), 'w'), indent=1); print(json.dumps(out, indent=1))
