#!/usr/bin/env python3
"""Phase XII, Part V: the one-child intervention T_{c,pi}: replace the frame permutation of child slot c by pi.

For each preregistered base (FR30 = 4752; 4753, a member of class 1387) and each of its single-child neighbours
(phase11_preregistration.json, part_V_counterfactuals; one representative per S3-conjugation orbit), and R in (6, 8) (at R = 4, rho = R - 311/175 is below the largest panel distance 15/7 and the amplification degenerates):
  Lambda_R  the float bottom min over all legal R-balls of lambda_min(24 - A~) (the quantity certified in phase11_cert, here in
            floating point: an estimate of the certificate, not a certificate);
  D_R       the float bottom of the plain Dirichlet ball operators (an estimate of the upper bound D_R).
Delta(R) = Lambda_R(T r) - Lambda_R(r).  Also recorded: the changed slot and permutation.
Cost cap: R = 8 only for rules with at most 150 legal 1-star types (some FR30 neighbours have up to ~740 types).
Usage: python -u -I audit/phase12_intervention.py [R ...] -> audit/results/phase12_intervention.jsonl (resumable)"""
import os, sys, json, math, time, types
sys.modules.setdefault('resource', types.SimpleNamespace(getrusage=lambda *a: types.SimpleNamespace(ru_maxrss=0), RUSAGE_SELF=0))
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); RES = os.path.join(HERE, 'results')
from fractions import Fraction
import numpy as np, scipy.linalg as sl
import phase11_chair as C, phase11_frontier as F
OUT = os.path.join(RES, 'phase12_intervention.jsonl')
T0 = time.time()

def bottoms(spec, R, m=3):
    dec = C.rule(spec); types_, _, _ = C.legal_types(dec)
    balls, info = C.enumerate_balls(dec, R, m, types_, 1)
    assert info['rejected'] == 0
    rho = Fraction(R) - C.RC_BOUND; d2s = set()
    for G, T, c in types_.values():
        P = C.Patch(G, T); a, b, _ = P.panels(); X = C.centroid14(G, T); d2s |= set(((X[a] - X[b]) ** 2).sum(1).tolist())
    tab = C.amp_table_exact(rho, d2s); lam, dd = [], []
    for G, T, _ in balls.values():
        Ha, Hp, _ = C.ball_amplified(G, T, rho, tab.__getitem__)
        lam.append(sl.eigh(Ha.toarray(), eigvals_only=True, subset_by_index=[0, 0])[0])
        dd.append(sl.eigh(Hp.toarray(), eigvals_only=True, subset_by_index=[0, 0])[0])
    return {'balls': info['distinct'], 'types': len(types_), 'Lambda_float': float(min(lam)), 'D_float': float(min(dd))}

def changed_slot(base, j):
    d0 = C.proper_decoration(int(base)); d1 = C.extended_decoration(j)
    # the neighbour is one S3-conjugation representative: compare with every conjugate of the base
    for Q in C.PERMS:
        e = F.conj_decoration(d0, Q); diff = [c for c in range(8) if e[c] != d1[c]]
        if len(diff) <= 1: return {'conjugation': list(Q), 'slot': diff[0] if diff else None, 'from': list(e[diff[0]]) if diff else None, 'to': list(d1[diff[0]]) if diff else None}
    return None

if __name__ == '__main__':
    os.environ.setdefault('OMP_NUM_THREADS', '1')
    Rs = [int(x) for x in sys.argv[1:]] or [6, 8]
    pre = json.load(open(os.path.join(RES, 'phase11_preregistration.json')))['part_V_counterfactuals']
    done = set()
    if os.path.exists(OUT):
        for l in open(OUT): r = json.loads(l); done.add((r['base'], r['j'], r['R']))
    jobs = []
    for R in Rs:                                   # all rules at the smaller radius first; at larger radii the rules with the
        js = []                                    # fewest legal types (cheapest) first, from the smaller-radius records
        for base, nbs in (('4752', pre['neighbours_FR30']), ('4753', pre['neighbours_4753'])):
            js += [(base, F.ext_index(C.proper_decoration(int(base))))] + [(base, j) for j in nbs]
        if os.path.exists(OUT):
            nt = {r['j']: r['types'] for r in map(json.loads, open(OUT))}
            js.sort(key=lambda bj: nt.get(bj[1], 10 ** 6))
        if R > min(Rs) and os.path.exists(OUT):          # cost cap (stated in the report): larger radii only for rules with at
            js = [bj for bj in js if nt.get(bj[1], 0) <= 150]   # most 150 legal 1-star types; the others are recorded at R = 6
        jobs += [(b, j, R) for b, j in js]
    for base, j, R in jobs:
        if (base, j, R) in done: continue
        if R > min(Rs):
            nt = {r['j']: r['types'] for r in map(json.loads, open(OUT))} if os.path.exists(OUT) else {}
            if nt.get(j, 10 ** 6) > 150: continue                     # the cost cap, decided from the R = 6 record
        t = time.time(); r = bottoms('x%d' % j, R)
        rec = {'base': base, 'j': j, 'R': R, **r, 'change': changed_slot(base, j), 'seconds': time.time() - t}
        with open(OUT, 'a') as fh: fh.write(json.dumps(rec) + '\n')
        print(f"[{time.time() - T0:7.0f}s] {base} {j} R={R} {r}", flush=True)
