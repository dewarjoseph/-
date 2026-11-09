#!/usr/bin/env python3
"""Phase XV companion (NOT preregistered; exploratory [E]): the boundary weight of the FREE (Neumann) copy states.

The preregistered measurement (phase15_boundary_weight.py) concerns the pinned copy states, which enter only the upper-bound side.
The lower-bound side of one-step bracketing uses the free operator F = Deg - A_U on each copy (Phase X, Theorem X.2: F_k <= E_*),
because on the hull 24 - A_U = (direct sum of the free pieces) + V_glue with V_glue >= 0.  This script measures, for the lowest
free states of a copy of T_L inside T_{L+1} (rule 1387, L = 2..5):
  w_Gamma = weight on the copy's tiles incident to Gamma_L;   w_bdry = weight on the copy's tiles with deg_copy < 24 (all of its surface)
  lambda_F = lambda_min(F on T_L)  (Phase X's F_L)
Usage: python -u -I audit/phase15_neumann_weight.py [Lmax=5] -> audit/results/phase15_neumann_weight.json"""
import os, sys, json, time, types
os.environ.setdefault('OMP_NUM_THREADS', '1')
sys.modules.setdefault('resource', types.SimpleNamespace(getrusage=lambda *a: types.SimpleNamespace(ru_maxrss=0), RUSAGE_SELF=0))
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); RES = os.path.join(HERE, 'results')
import numpy as np
import phase11_chair as C, phase15_boundary_weight as B
OUT = os.path.join(RES, 'phase15_neumann_weight.json'); T0 = time.time()
def log(*a): print(f'[{time.time() - T0:7.0f}s]', *a, flush=True)

def level(dec, L):
    G, T, n, a, b, k, copy, gam = B.geometry(dec, L); m = 8 ** L
    nG = np.bincount(a[gam], minlength=n) + np.bincount(b[gam], minlength=n)
    G0, T0_ = C.supertile(dec, L); F = C.operators(G0, T0_, free=True)                   # Deg - A_U on T_L (natural order)
    P = C.Patch(G0, T0_); a0, b0, _ = P.panels(); deg = np.bincount(a0, minlength=m) + np.bincount(b0, minlength=m)
    w, V, info = B.bottom(F); rec = {'L': L, 'lambda_F': [float(x) for x in w], 'solver': info,
                                     'surface_tiles': int((deg < 24).sum()), 'tiles': m, 'copies': []}
    for c in range(8):
        inc = nG[c * m:(c + 1) * m] > 0; st = []
        for j in range(B.K):
            p2 = (np.abs(V[:, j].reshape(-1, 2)) ** 2).sum(1); p2 /= p2.sum()
            st.append({'w_Gamma': float(p2[inc].sum()), 'w_bdry': float(p2[deg < 24].sum())})
        rec['copies'].append({'copy': c, 'incident_tiles': int(inc.sum()), 'states': st})
    rec['w_Gamma_max'] = [max(cr['states'][j]['w_Gamma'] for cr in rec['copies']) for j in range(B.K)]
    rec['w_bdry'] = [rec['copies'][0]['states'][j]['w_bdry'] for j in range(B.K)]
    rec['uniform_w_bdry'] = rec['surface_tiles'] / m
    log(f'L={L}: lambda_F {rec["lambda_F"]}, w_Gamma_max {rec["w_Gamma_max"]}, w_bdry {rec["w_bdry"]}, uniform {rec["uniform_w_bdry"]:.4f}')
    return rec

if __name__ == '__main__':
    Lmax = int(sys.argv[1]) if len(sys.argv) > 1 else 5; dec = C.rule('1387'); recs = {L: level(dec, L) for L in range(2, Lmax + 1)}
    Ls = sorted(recs)
    out = {'rule': '1387', 'label': '[E], not preregistered (exploratory companion of phase15_boundary_weight.py)', 'levels': recs,
           'fit_w_Gamma_max_k0': B.fit(Ls, [recs[L]['w_Gamma_max'][0] for L in Ls]),
           'fit_w_bdry_k0': B.fit(Ls, [recs[L]['w_bdry'][0] for L in Ls])}
    json.dump(out, open(OUT, 'w'), indent=1); log('fits', out['fit_w_Gamma_max_k0'], out['fit_w_bdry_k0'])
