#!/usr/bin/env python3
"""Phase XI, Part II, stage X6: for the X5 survivors outside the right-S3 orbit of 1387, the minimum over all legal 8-balls of
the pinned bottom (D_8), certified from above by the exact rational Rayleigh quotient on the minimising ball.  Same elimination
rule as X3-X5 (an exact upper bound on a legal patch below L_ref = 8.7999987).
Usage: python -u -I audit/phase11_d8stage.py <x-spec> ... -> audit/results/phase11_frontier_X6.jsonl"""
import os, sys, json, time, math, types
sys.modules.setdefault('resource', types.SimpleNamespace(getrusage=lambda *a: types.SimpleNamespace(ru_maxrss=0), RUSAGE_SELF=0))
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); RES = os.path.join(HERE, 'results')
import numpy as np
from fractions import Fraction
import phase11_chair as C, phase11_frontier as F
def lam(args):
    G, T = args; H = C.operators(G.astype(np.int64), T.astype(np.int64)); return float(np.linalg.eigvalsh(H.toarray())[0])
if __name__ == '__main__':
    import multiprocessing as mp
    for spec in sys.argv[1:]:
        t0 = time.time(); dec = C.rule(spec); ty, n0, _ = C.legal_types(dec); balls, info = C.enumerate_balls(dec, 8, 3, ty, nproc=4)
        items = list(balls.values())
        with mp.Pool(4) as pool: lp = pool.map(lam, [(G, T) for G, T, _ in items], chunksize=16)
        i = int(np.argmin(lp)); G, T, _ = items[i]; H = C.operators(G.astype(np.int64), T.astype(np.int64))
        w, V = np.linalg.eigh(H.toarray()); num, den = F.exact_upper(H, V[:, 0])
        rec = {'spec': spec, 'j': int(spec[1:]), 'types': len(ty), 'types_T5': n0, 'frame_graph': C.frame_graph(dec), 'balls': info['distinct'], 'rejected': info['rejected'],
               'D8_float': float(lp[i]), 'D8_upper_exact': f'{num}/{den}', 'D8_upper': num / den,
               'inferior': num * F.L_REF.denominator < F.L_REF.numerator * den, 'seconds': time.time() - t0}
        print(rec, flush=True)
        with open(os.path.join(RES, 'phase11_frontier_X6.jsonl'), 'a') as f: f.write(json.dumps(rec) + '\n')
