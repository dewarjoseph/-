#!/usr/bin/env python3
"""Phase XII, section 14.3 [X]: how much of the localisation cost is the IMS constant, and how much is the rate.

1. The first Dirichlet eigenvalue of the continuum chair (the unit cube minus the octant [1/2, 1]^3), by 7-point finite differences
   at h = 1/16, 1/32, 1/48, extrapolated in h with the exponents 4/3 (re-entrant edges) and 2; the unit cube is the control (3 pi^2).
2. The upper model of phase12_extrapolation (Y_L = E + A q^L, E = E_up) read as a Dirichlet problem on T_7, a chair of side
   2^8 = 256 (cube units, the units of the IMS radius R): Y_7 - E_up = kappa_eff * lambda_1(chair) / 256^2 defines an effective
   kinetic constant of the low-energy states.  The IMS fits Lambda_R = E - C / rho^2 correspond to kappa = C / pi^2 (a ball of radius
   rho).  A localisation as good as the low-energy states themselves would have C = kappa_eff * pi^2.
Everything here is a model estimate [X].  Usage: python -u -I audit/phase12_chair_dirichlet.py -> audit/results/phase12_chair_dirichlet.json"""
import os, json, math
import numpy as np, scipy.sparse as sp, scipy.sparse.linalg as sla
HERE = os.path.dirname(os.path.abspath(__file__)); RES = os.path.join(HERE, 'results')

def lam(n, chair=True):
    h = 1.0 / n; c = np.arange(1, n) * h
    X, Y, Z = np.meshgrid(c, c, c, indexing='ij')
    inside = ~((X >= 0.5) & (Y >= 0.5) & (Z >= 0.5)) if chair else np.ones_like(X, bool)
    idx = -np.ones(X.shape, int); idx[inside] = np.arange(inside.sum()); N = int(inside.sum()); rows, cols = [], []
    for ax in range(3):
        for s in (1, -1):
            nb = np.roll(idx, -s, axis=ax); sl = [slice(None)] * 3; sl[ax] = slice(-1, None) if s == 1 else slice(0, 1); nb[tuple(sl)] = -1
            m = (idx >= 0) & (nb >= 0); rows.append(idx[m]); cols.append(nb[m])
    r, cc = np.concatenate(rows), np.concatenate(cols)
    A = (sp.csr_matrix((-np.ones(len(r)), (r, cc)), shape=(N, N)) + 6 * sp.eye(N)).tocsc() / h ** 2
    return float(sla.eigsh(A, k=1, sigma=0, which='LM', return_eigenvectors=False)[0])

if __name__ == '__main__':
    grid = {n: {'chair': lam(n), 'cube': lam(n, False)} for n in (16, 32, 48)}
    a, b = grid[32]['chair'], grid[48]['chair']
    ext = {p: b - (a - b) / ((48 / 32) ** p - 1) for p in (4 / 3, 2)}
    lam1 = sum(ext.values()) / 2
    X = json.load(open(os.path.join(RES, 'phase12_extrapolation.json')))
    out = {'grid': grid, 'cube_exact_3pi2': 3 * math.pi ** 2, 'chair_lambda1_extrapolated': {'p=4/3': ext[4 / 3], 'p=2': ext[2]},
           'chair_lambda1_used': lam1, 'rules': {}}
    for n in ('1387', '539311', '1389'):
        y7, eup = X['Y'][n]['7'], X['E_up'][n]['E_up']; k = (y7 - eup) / (lam1 / 256 ** 2); C = X['E_low'][n]['C']
        out['rules'][n] = {'Y7_minus_E_up': y7 - eup, 'kappa_eff': k, 'C_ideal': k * math.pi ** 2, 'C_IMS_fit': C, 'kappa_IMS': C / math.pi ** 2}
    json.dump(out, open(os.path.join(RES, 'phase12_chair_dirichlet.json'), 'w'), indent=1)
    print(json.dumps(out, indent=1))
