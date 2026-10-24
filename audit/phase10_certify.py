#!/usr/bin/env python3
"""Phase X: a rigorous bracket for the floor of EVERY gauge class, by Dirichlet-Neumann bracketing.

  lower  E_*(r) >= lambda_min H_free(T_3(r))   certified: floating Cholesky of the real form of H_free - mu, Higham Thm 10.3
         (H_free has Gaussian-integer entries; mu a 20-bit dyadic below the float bottom)
  upper  E_*(r) <= lambda_min H_pin(T_4(r))   certified: exact rational Rayleigh quotient of an integer vector (T_4 is a
         legal patch of every tiling of a minimal hull, so a compression); sharper level-5 uppers are certified in stage B
(The perturbation sensitivity of each class is computed from the census in phase10_analysis.py.)
Usage: python -u -I audit/phase10_certify.py [nproc] -> audit/results/phase10_certify.jsonl (resumable)"""
import os, sys, json, time, math, types
from fractions import Fraction
sys.modules.setdefault('resource', types.SimpleNamespace(getrusage=lambda *a: types.SimpleNamespace(ru_maxrss=0), RUSAGE_SELF=0))
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); RES = os.path.join(HERE, 'results')
import numpy as np
import phase9_pair as P9
import phase10_census as C
T0 = time.time()
def log(*a): print(f"[{time.time()-T0:7.0f}s]", *a, flush=True)
OUT = os.path.join(RES, 'phase10_certify.jsonl')

def job(cls):
    dec = P9.decoration(cls); rec = {'class': cls}
    S3 = P9.build([dec] * 3); Hf = C.free_op(S3); f3 = float(np.linalg.eigvalsh(Hf.toarray())[0])
    mu = Fraction(math.floor((f3 - 1e-7) * 2 ** 20), 2 ** 20); rec['F3_float'] = f3; rec['F3_certified_lower'] = P9.certified_lower(Hf, mu)
    S4 = P9.build([dec] * 4); q4 = P9.rayleigh_upper(S4['H']); rec['Y4_upper_exact'] = f'{q4.numerator}/{q4.denominator}'; rec['Y4_upper'] = float(q4)
    rec['certified_upper'] = rec['Y4_upper']; rec['certified_lower'] = rec['F3_certified_lower']
    return rec

if __name__ == '__main__':
    import multiprocessing as mp
    nproc = int(sys.argv[1]) if len(sys.argv) > 1 else 12
    cen = json.load(open(os.path.join(RES, 'phase10_census.json')))['classes']; classes = [r['class'] for r in cen]
    done = {json.loads(l)['class'] for l in open(OUT)} if os.path.exists(OUT) else set()
    todo = [c for c in classes if c not in done]; log(f"{len(todo)} classes to certify")
    with mp.Pool(nproc) as pool, open(OUT, 'a') as f:
        for i, r in enumerate(pool.imap_unordered(job, todo, chunksize=2)):
            f.write(json.dumps(r) + '\n'); f.flush()
            if i % 100 == 0: log(f"{i + 1}/{len(todo)} class {r['class']}: [{r['certified_lower']:.4f}, {r['certified_upper']:.4f}]")
