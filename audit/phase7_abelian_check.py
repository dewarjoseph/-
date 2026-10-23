#!/usr/bin/env python3
"""Phase VII (II.3): independent re-derivation of the upper side of the FR30-vs-Z2 comparison, same normalisation.

Operator: H = 24 - A_U on l^2(tiles) (x) C^2 of the infinite chair tiling (every tile has 24 panels, so pinned = free there).
For a level-L supertile, (24 - A_U)|T_L is a principal submatrix of the infinite operator, so inf spec H_inf <= lambda_min(H|T_L)
<= any Rayleigh quotient on T_L.  Frames are generated with phase7_local.gen_poses (substitution ops D_s(v) P(pi_v)), links with
independent_clifford_q8_audit.clifford_link -- no phase6_* code.  The exact upper certificate is the Rayleigh quotient of a
Gaussian-integer vector (scaled, rounded float eigenvector), evaluated in exact integer arithmetic.
Systems: A trivial links (U = 1), B reflection-only frames (pi = id: links +-1, Abelian Z2), C FR30.
Usage: python -u -I audit/phase7_abelian_check.py -> audit/results/phase7_abelian_check.json"""
import os, sys, json, time
from fractions import Fraction
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); RES = os.path.join(HERE, 'results')
import numpy as np, scipy.sparse as sps, scipy.sparse.linalg as sla
import phase7_local as P
from independent_clifford_q8_audit import FR30, clifford_link
T0 = time.time()
def log(*a): print(f"[{time.time()-T0:6.0f}s]", *a, flush=True)
REFLECTION_ONLY = {'0': (0, 1, 2), **{v: (0, 1, 2) for v in FR30 if v != '0'}}

def operator(dec, level, trivial=False):
    """integer sparse Re, Im of 24 - A_U on T_level, plus the fraction of -1 links and whether all links are +-1."""
    ops = P.make_ops(dec); P.GOPS = np.array([g for g, t in ops]); P.TOPS = np.array([t for g, t in ops])
    G, T = P.gen_poses(level); grid = P.owner_grid(level, G, T); n = len(G); N = grid.shape[0]
    rows, cols, re, im = [], [], [], []; nlinks = 0; minus = 0; abelian = True
    for ax in range(3):
        sl_a = [slice(None)] * 3; sl_b = [slice(None)] * 3; sl_a[ax] = slice(0, N - 1); sl_b[ax] = slice(1, N)
        A, B = grid[tuple(sl_a)].ravel(), grid[tuple(sl_b)].ravel(); m = (A >= 0) & (B >= 0) & (A != B)
        nv = np.zeros(3, int); nv[ax] = 1
        for a, b in zip(A[m], B[m]):
            C = np.eye(2) if trivial else clifford_link(np.asarray(G[a], int), np.asarray(G[b], int), nv)
            Cr, Ci = np.rint(C.real).astype(int), np.rint(C.imag).astype(int); assert np.allclose(C, Cr + 1j * Ci)
            nlinks += 1; minus += bool(np.allclose(C, -np.eye(2))); abelian &= bool(np.allclose(C, np.eye(2)) or np.allclose(C, -np.eye(2)))
            for i in range(2):
                for j in range(2):
                    if Cr[i, j] or Ci[i, j]:
                        rows += [2 * a + i, 2 * b + j]; cols += [2 * b + j, 2 * a + i]; re += [-Cr[i, j], -Cr[i, j]]; im += [-Ci[i, j], Ci[i, j]]
    d = np.arange(2 * n); rows += list(d); cols += list(d); re += [24] * (2 * n); im += [0] * (2 * n)
    Re = sps.csr_matrix((re, (rows, cols)), shape=(2 * n, 2 * n), dtype=np.int64); Im = sps.csr_matrix((im, (rows, cols)), shape=(2 * n, 2 * n), dtype=np.int64)
    assert (Re != Re.T).nnz == 0 and (Im + Im.T).nnz == 0
    return Re, Im, {'tiles': n, 'panels': nlinks, 'minus_one_fraction': minus / nlinks, 'abelian': abelian}

def rayleigh_upper(Re, Im, scale=2 ** 20):
    H = (Re + 1j * Im).astype(complex); w, V = sla.eigsh(H, k=1, which='SA', tol=1e-12); v = V[:, 0] / np.abs(V[:, 0]).max()
    xr = np.rint(v.real * scale).astype(np.int64); xi = np.rint(v.imag * scale).astype(np.int64)
    yr = Re @ xr - Im @ xi; yi = Re @ xi + Im @ xr                      # (Re + i Im)(xr + i xi), exact in int64 (|entries| <= 2^26)
    num = sum(int(a) * int(b) for a, b in zip(xr, yr)) + sum(int(a) * int(b) for a, b in zip(xi, yi))
    den = sum(int(a) * int(a) for a in xr) + sum(int(a) * int(a) for a in xi)
    q = Fraction(num, den); return float(w[0]), q

if __name__ == '__main__':
    out = {}
    for name, dec, triv in (('trivial', FR30, True), ('reflection_only_Z2', REFLECTION_ONLY, False), ('fr30', FR30, False)):
        out[name] = {}
        for level in (2, 3, 4, 5):
            Re, Im, info = operator(dec, level, triv); lam, q = rayleigh_upper(Re, Im)
            out[name][level] = {**info, 'lambda_min_float': lam, 'rayleigh_upper_exact': f'{q.numerator}/{q.denominator}', 'rayleigh_upper': float(q)}
            log(f"{name} L{level}: {info}; lambda_min {lam:.10f}; exact Rayleigh upper {float(q):.10f}")
    json.dump(out, open(os.path.join(RES, 'phase7_abelian_check.json'), 'w'), indent=1)
