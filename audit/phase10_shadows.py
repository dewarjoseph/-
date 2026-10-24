#!/usr/bin/env python3
"""Phase X: the Abelian-shadow benchmark for any decoration.

chi_k o U (k = 1, 2, 3, as in Phase VII-B): every link U in Q8 is replaced by chi_k(U) I_2, where chi_k: Q8 -> {+1, -1} has kernel
<q_k> (chi_k(+-1) = chi_k(+-q_k) = +1, chi_k(+-q_j) = -1 for j != k; q_k = -i sigma_k, axis k - 1 in phase9_pair.q8class).  Then H = H_s (x) I_2 with H_s = 24 - A_s real symmetric.
Geometry, hierarchy, normalisation and boundary conditions are those of the non-Abelian rule; only the links change.  Phase
VII-B computed FR30's shadows (phase7b_scaling.json); this reproduces them and adds the stage-B candidates.
Per decoration and k: Y_L for L = 3..L_max (pinned supertile bottoms, upper bounds on the shadow's floor) and the exact rational
Rayleigh quotient at L_max (a certified upper bound on E_*(chi_k o U)).
Usage: python -u -I audit/phase10_shadows.py <L_max> <decoration> [...] -> audit/results/phase10_shadows.json (merged)"""
import os, sys, json, time, types
sys.modules.setdefault('resource', types.SimpleNamespace(getrusage=lambda *a: types.SimpleNamespace(ru_maxrss=0), RUSAGE_SELF=0))
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); RES = os.path.join(HERE, 'results')
import numpy as np, scipy.sparse as sps
import phase9_pair as P9
T0 = time.time()
def log(*a): print(f"[{time.time()-T0:7.0f}s]", *a, flush=True)
OUT = os.path.join(RES, 'phase10_shadows.json')

def shadow_scalar(S, k):
    """H_s = 24 - A_s on the supertile S (duplicate panels between a tile pair add, as in the non-Abelian operator)"""
    c = P9.q8class(P9.links(S['G'], S['a'], S['b'], S['ax'])); chi = np.where((c >= 10) | (c == k), 1.0, -1.0); n = S['n']
    A = sps.csr_matrix((np.r_[chi, chi], (np.r_[S['a'], S['b']], np.r_[S['b'], S['a']])), shape=(n, n))
    return (24 * sps.identity(n, format='csr') - A).tocsr()

if __name__ == '__main__':
    Lmax = int(sys.argv[1]); out = json.load(open(OUT)) if os.path.exists(OUT) else {}
    for d in map(int, sys.argv[2:]):
        dec = P9.decoration(d); rec = {}
        for L in range(3, Lmax + 1):
            S = P9.build([dec] * L)
            for k in range(3):
                Hs = shadow_scalar(S, k); rec.setdefault(f'chi{k + 1}', {})[f'Y{L}'] = P9.lam_min(Hs)
                if L == Lmax:
                    q = P9.rayleigh_upper(Hs); rec[f'chi{k + 1}'][f'Y{L}_upper_exact'] = f'{q.numerator}/{q.denominator}'; rec[f'chi{k + 1}'][f'Y{L}_upper'] = float(q)
            log(d, L, {k: round(v[f'Y{L}'], 6) for k, v in rec.items()})
        out[str(d)] = rec; json.dump(out, open(OUT, 'w'), indent=1)
