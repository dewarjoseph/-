#!/usr/bin/env python3
"""Phase VIII (section 5.3): the next member of the selection chain, U_m(tau_59) = lambda_min of the pinned operator on
sigma^m(tau_59), with an exact integer Rayleigh certificate (E_* <= U_m(tau) by compression to a legal patch; the certificate is
the exact rational Rayleigh quotient of the rounded float eigenvector, hence a rigorous upper bound on lambda_min and on E_*).
Usage: python -u -I audit/phase8_chain5.py m [type] -> audit/results/phase8_chain_m<m>.json"""
import os, sys, json, time
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); RES = os.path.join(HERE, 'results')
import numpy as np, scipy.sparse.linalg as sla
from fractions import Fraction
import phase7_local as P
from phase8_env_fiber import patch_operator
from phase8_patch_bounds import types_sorted
T0 = time.time()
def log(*a): print(f"[{time.time()-T0:7.0f}s]", *a, flush=True)

if __name__ == '__main__':
    m = int(sys.argv[1]); j = int(sys.argv[2]) if len(sys.argv) > 2 else 59
    tau = types_sorted()[j]; poses, c = P.poses_from_key(tau)
    for _ in range(m): poses = P.inflate(poses)
    log(f"type {j}, m = {m}: {len(poses)} tiles"); H = patch_operator(poses).tocsr(); log(f"operator dim {H.shape[0]}, nnz {H.nnz}")
    w, V = sla.eigsh(H, k=2, which='SA', tol=1e-10, ncv=48); i = int(np.argmin(w)); v = V[:, i]; lam = float(w[i])
    res = float(np.linalg.norm(H @ v - lam * v)); log(f"lambda_min = {lam:.10f} (residual {res:.1e})")
    v = v / np.abs(v).max(); Re = H.real.tocsr(); Im = H.imag.tocsr(); Re.data = np.rint(Re.data); Im.data = np.rint(Im.data)
    Re = Re.astype(np.int64); Im = Im.astype(np.int64); scale = 2 ** 22
    xr = np.rint(v.real * scale).astype(np.int64); xi = np.rint(v.imag * scale).astype(np.int64)
    yr = Re @ xr - Im @ xi; yi = Re @ xi + Im @ xr
    num = sum(int(a) * int(b) for a, b in zip(xr, yr)) + sum(int(a) * int(b) for a, b in zip(xi, yi)); den = sum(int(a) * int(a) for a in xr) + sum(int(a) * int(a) for a in xi)
    q = Fraction(num, den); log(f"exact Rayleigh certificate: E_* <= {float(q):.10f}")
    json.dump({'type': j, 'm': m, 'tiles': len(poses), 'lambda_float': lam, 'residual': res, 'rayleigh_upper_exact': f'{q.numerator}/{q.denominator}', 'rayleigh_upper': float(q),
               'seconds': time.time() - T0}, open(os.path.join(RES, f'phase8_chain_m{m}.json'), 'w'), indent=1)
