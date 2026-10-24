#!/usr/bin/env python3
"""Phase XI: an independent exact upper bound on E_*(FR30) from inflated legal 1-stars (the Phase VIII chain idea,
re-implemented): U_m(tau) = lambda_min of the pinned sigma^m(tau), a legal patch, hence >= E_*.  The type minimising U_3 is
inflated further; the bound is the exact rational Rayleigh quotient of the rounded eigenvector.
Usage: python -u -I audit/phase11_fr30_upper.py [m_max] -> audit/results/phase11_fr30_upper.json"""
import os, sys, json, time, types
sys.modules.setdefault('resource', types.SimpleNamespace(getrusage=lambda *a: types.SimpleNamespace(ru_maxrss=0), RUSAGE_SELF=0))
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); RES = os.path.join(HERE, 'results')
import numpy as np, scipy.sparse.linalg as sla
import phase11_chair as C, phase11_frontier as F
T0 = time.time()
def log(*a): print(f"[{time.time()-T0:7.0f}s]", *a, flush=True)
def lowest(H, tol=1e-12):
    if H.shape[0] <= 2000:
        w, V = np.linalg.eigh(H.toarray()); return float(w[0]), V[:, 0]
    w, V = sla.eigsh(H, k=1, which='SA', tol=tol, ncv=48, maxiter=200000); return float(w[0]), V[:, 0]
if __name__ == '__main__':
    mmax = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    dec = C.rule(4752); types_, _, phimap = C.legal_types(dec); keys = list(types_)
    selfloop = [i for i, k in enumerate(keys) if k in phimap[k]]
    rows = []
    for i, k in enumerate(keys):
        G, T, c = types_[k]
        for _ in range(3): G, T = C.inflate(G, T, dec)
        lam, _ = lowest(C.operators(G, T)); rows.append((lam, i))
    rows.sort(); best = rows[0][1]; log('U3 lowest', rows[:4], 'self-loop types', len(selfloop), 'best is self-loop:', best in selfloop)
    out = {'U3_lowest': rows[:6], 'best_type': best, 'best_is_selfloop': best in selfloop, 'chain': []}
    G, T, c = types_[keys[best]]
    for m in range(1, mmax + 1):
        G, T = C.inflate(G, T, dec)
        if m < 3: continue
        H = C.operators(G, T); lam, v = lowest(H); num, den = F.exact_upper(H, v)
        out['chain'].append({'m': m, 'tiles': int(len(G)), 'lambda_float': lam, 'upper_exact': f'{num}/{den}', 'upper': num / den})
        log(out['chain'][-1]); json.dump(out, open(os.path.join(RES, 'phase11_fr30_upper.json'), 'w'), indent=1)
