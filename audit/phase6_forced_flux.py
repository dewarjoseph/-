#!/usr/bin/env python3
"""Phase VI, Theorem F (forced frustration and a uniform spectral floor): exhaustive level-1 verification.

Every geometry-compatible, orientation-preserving frame choice for the 8 children of a chair is one of the 3^8 = 6561 parity-
admissible decorations (the 3 rotations of each parity class differ by the chair's rotation stabilizer C3; Proposition E0 of
Phase V-E).  For each decoration d this script computes, on the level-1 supertile (8 tiles, 48 panels):
  - whether the Clifford connection is pure gauge (all fundamental-cycle holonomies = +1), the holonomy group, plaquette classes;
  - m(d) = lambda_min of the free (Neumann) connection Laplacian L_U = D_U^dagger D_U  (16 x 16), in floating point;
and then CERTIFIES in exact rational arithmetic that  L_U(d) - c I  is positive definite for every d, with c a rational just
below min_d m(d) (exact LDL^T of the real 32 x 32 form [[Re, -Im], [Im, Re]], entries in Z, c in Q).
Usage: python -u -I audit/phase6_forced_flux.py      -> audit/results/phase6_forced_flux.json
"""
import os, sys, json, time, itertools, collections
from fractions import Fraction
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); RES = os.path.join(HERE, 'results')
import numpy as np
import phase6_gauge_audit as G

EVEN = [p for p in itertools.permutations(range(3)) if round(np.linalg.det(G.P(p))) == 1]
ODD = [p for p in itertools.permutations(range(3)) if round(np.linalg.det(G.P(p))) == -1]
def decoration(i):
    dig = []
    for _ in range(8): dig.append(i % 3); i //= 3
    dec = {'0': EVEN[dig[0]]}
    for k, v in enumerate(G.U3): dec[v] = (EVEN if sum(v) % 2 == 0 else ODD)[dig[k + 1]]
    return dec

def exact_posdef(L_int_re, L_int_im, c):
    """exact test that the Hermitian matrix L - c I (L = Re + i Im with integer parts) is positive definite (LDL^T, no pivoting)."""
    n = L_int_re.shape[0]; N = 2 * n
    A = [[Fraction(0)] * N for _ in range(N)]
    for i in range(n):
        for j in range(n):
            re, im = int(L_int_re[i, j]), int(L_int_im[i, j])
            A[i][j] = Fraction(re); A[i + n][j + n] = Fraction(re); A[i][j + n] = Fraction(-im); A[i + n][j] = Fraction(im)
    for i in range(N): A[i][i] -= c
    for k in range(N):
        if A[k][k] <= 0: return False
        piv = A[k][k]
        for i in range(k + 1, N):
            if A[i][k] == 0: continue
            f = A[i][k] / piv
            for j in range(k + 1, N): A[i][j] -= f * A[k][j]
    return True

def main():
    t0 = time.time(); recs = []; tl0 = None
    for i in range(3 ** 8):
        dec = decoration(i); tl = G.tiles(dec, 1); pn = G.panels(tl); n = len(tl)
        links = [G.link(tl[a][0], tl[b][0], k) for a, b, k, _ in pn]
        deg = np.zeros(n)
        for a, b, k, _ in pn: deg[a] += 1; deg[b] += 1
        _, cycles = G.tree_and_cycles(n, pn); Ws = [G.holonomy(pn, links, c) for c in cycles]
        cls = collections.Counter(G.qclass(W) for W in Ws)
        L = G.operator(tl, pn, links, deg).toarray(); w = np.linalg.eigvalsh(L)
        plq = G.plaquette_census(tl, pn, links)
        recs.append({'index': i, 'nontrivial_cycles': int(len(Ws) - cls['+1']), 'cycle_classes': dict(cls), 'plaquettes': plq,
                     'free_lambda_min': float(w[0]), 'L': L})
    geo_same = len({(len(G.panels(G.tiles(decoration(i), 1)))) for i in (0, 100, 6560)}) == 1
    m = np.array([r['free_lambda_min'] for r in recs]); imin = int(np.argmin(m)); mmin = float(m.min())
    c = Fraction(int(np.floor(mmin * 1000)) - 1, 1000)               # rational strictly below the minimum
    cert_fail = []; t1 = time.time()
    for r in recs:
        L = r.pop('L'); Re = np.rint(L.real).astype(int); Im = np.rint(L.imag).astype(int)
        assert np.abs(L.real - Re).max() < 1e-12 and np.abs(L.imag - Im).max() < 1e-12
        if not exact_posdef(Re, Im, c): cert_fail.append(r['index'])
    out = {'decorations': len(recs), 'pure_gauge_count': int(sum(r['nontrivial_cycles'] == 0 for r in recs)),
           'min_nontrivial_cycles': int(min(r['nontrivial_cycles'] for r in recs)), 'max_nontrivial_cycles': int(max(r['nontrivial_cycles'] for r in recs)),
           'free_lambda_min': {'min': mmin, 'argmin_decoration': imin, 'max': float(m.max()), 'median': float(np.median(m)),
                               'fr30': float(m[[i for i in range(len(recs)) if decoration(i) == G.FR30][0]])},
           'certified_lower_bound': {'c': f'{c.numerator}/{c.denominator}', 'value': float(c), 'all_certified': not cert_fail, 'failures': cert_fail[:20],
                                     'method': 'exact rational LDL^T of L_U - c I (real 32x32 form) for all 6561 decorations'},
           'min_minus1_plaquettes': int(min(r['plaquettes'].get('-1', 0) for r in recs)), 'min_traceless_plaquettes': int(min(r['plaquettes'].get('traceless', 0) for r in recs)),
           'distinct_spectra_min_values': len(set(np.round(m, 10))), 'seconds_float': t1 - t0, 'seconds_exact': time.time() - t1,
           'per_decoration': [{k: v for k, v in r.items()} for r in recs]}
    json.dump(out, open(os.path.join(RES, 'phase6_forced_flux.json'), 'w'), indent=None)
    print(json.dumps({k: v for k, v in out.items() if k != 'per_decoration'}, indent=1))

if __name__ == '__main__': main()
