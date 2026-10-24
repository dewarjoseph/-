#!/usr/bin/env python3
"""Phase XI, Part II.4: the cost model of a localisation certificate for 1387 (decoration 4753) -- one legal ball per radius,
taken from the m = 5 inflation of 1-star type 31 (the lowest-U1 type), timed: ball construction and the banded Higham certificate
(RCM + dpbtrf) at mu = 8.5.  Per-ball times multiply the distinct-ball counts of phase11_cert.jsonl into a run time.
Usage: python -u -I audit/phase11_costs.py -> audit/results/phase11_costs.json  (times depend on load; the run is recorded with it)"""
import os, sys, time, json, numpy as np
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); RES = os.path.join(HERE, 'results')
from fractions import Fraction
import phase11_chair as C
if __name__ == '__main__':
    os.environ.setdefault('OMP_NUM_THREADS', '1')
    dec = C.rule('4753'); ty, _, _ = C.legal_types(dec); keys = list(ty); d2s = set()
    for G, T, c in ty.values():
        P = C.Patch(G, T); a, b, _ = P.panels(); X = C.centroid14(G, T); d2s |= set(((X[a] - X[b]) ** 2).sum(1).tolist())
    G0, T0, c = ty[keys[31]]
    t0 = time.time(); G, T, X, tree, ts, okm = C._inflated_patch(G0, T0, c, dec, 22, 5); tinf = time.time() - t0
    good = ts[okm]; out = {'rule': '4753', 'type': 31, 'inflate_m5_s': tinf, 'accepted_R22': int(okm.sum()), 'load_note': sys.argv[1] if len(sys.argv) > 1 else None}
    for R in (14, 16, 18, 20, 22):
        rho = Fraction(R) - C.RC_BOUND; tab = C.amp_table_exact(rho, d2s); err = 24 * max(tab.values()) * 2.0 ** -52
        t = good[len(good) // 2]; cand = tree.query_ball_point(X[t].astype(float), 14 * R + 1e-6)
        t1 = time.time(); kb, Gb, Tb = C._ball_at(G, T, X, cand, t, R); Ha, _, _ = C.ball_amplified(Gb, Tb, float(rho), tab.__getitem__); tb = time.time() - t1
        t1 = time.time(); low, bw = C.banded_cert(Ha, 8.5, err); tc = time.time() - t1
        out[str(R)] = {'tiles': len(Gb), 'build_s': tb, 'cholesky_s': tc, 'bandwidth': bw, 'passed_at_8.5': low is not None}
        print(R, out[str(R)], flush=True)
    json.dump(out, open(os.path.join(RES, 'phase11_costs.json'), 'w'), indent=1)
