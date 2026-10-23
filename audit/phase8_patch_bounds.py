#!/usr/bin/env python3
"""Phase VIII (section 5): spectral-edge selection by legal 1-star patches.

For a legal 1-star type tau (|V_1| = 72) and m >= 0, the patch sigma^m(tau) is a legal finite patch of every FR30 hull tiling
(Phase VII), and the pinned operator on it is the compression of the infinite-volume operator.  Hence
    U_m(tau) := lambda_min( (24 - A_U)|sigma^m(tau) )  >=  E_*  = inf spec H_FR30          (compression; Rayleigh-Ritz)
    U_m := min_tau U_m(tau) is non-increasing in m and U_m -> E_*:
      * non-increasing: sigma^m(tau) is the patch of the central tile's m-th descendants' neighbourhood; the 1-star of the
        central tile's parent (another legal type tau') satisfies sigma(tau') contains tau (closure lemma), so
        sigma^m(tau) is contained in sigma^(m+1)(tau') and interlacing gives U_(m+1)(tau') <= U_m(tau);
      * convergence: every legal ball lies in some sigma^m(tau) (Phase VII section 7 covering), and D_R -> E_*.
Which tau attains U_m ("edge-selecting configuration"), and whether it is a periodic point of the 1-star substitution
Phi (tau in Phi_c(tau) for a child index c, so that the patches nest), is recorded.  The best patch at the largest m gets an
exact integer Rayleigh certificate (rounded eigenvector, exact arithmetic).
Usage: python -u -I audit/phase8_patch_bounds.py [mmax] [nproc] -> audit/results/phase8_patch_bounds.json"""
import os, sys, json, time
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); RES = os.path.join(HERE, 'results')
import numpy as np, scipy.sparse.linalg as sla
from fractions import Fraction
T0 = time.time()
def log(*a): print(f"[{time.time()-T0:7.0f}s]", *a, flush=True)

def types_sorted():
    from phase7b_local_rules import legal_V1
    V1, _ = legal_V1(); return sorted(V1, key=lambda z: sorted(z))

def patch_bottom(args):
    j, m = args
    import phase7_local as P
    from phase8_env_fiber import patch_operator
    tau = types_sorted()[j]; poses, c = P.poses_from_key(tau)
    for _ in range(m): poses = P.inflate(poses)
    H = patch_operator(poses); w = sla.eigsh(H, k=2, which='SA', tol=1e-11, ncv=48, return_eigenvectors=False)
    return j, m, float(np.min(w)), H.shape[0] // 2

def certify(j, m):
    import phase7_local as P
    from phase8_env_fiber import patch_operator
    tau = types_sorted()[j]; poses, c = P.poses_from_key(tau)
    for _ in range(m): poses = P.inflate(poses)
    H = patch_operator(poses); w, V = sla.eigsh(H, k=2, which='SA', tol=1e-12, ncv=64); i = int(np.argmin(w)); v = V[:, i] / np.abs(V[:, i]).max()
    Re = H.real.tocsr(); Im = H.imag.tocsr(); Re.data = np.rint(Re.data); Im.data = np.rint(Im.data)
    Re = Re.astype(np.int64); Im = Im.astype(np.int64); scale = 2 ** 20
    xr = np.rint(v.real * scale).astype(np.int64); xi = np.rint(v.imag * scale).astype(np.int64)
    yr = Re @ xr - Im @ xi; yi = Re @ xi + Im @ xr
    num = sum(int(a) * int(b) for a, b in zip(xr, yr)) + sum(int(a) * int(b) for a, b in zip(xi, yi)); den = sum(int(a) * int(a) for a in xr) + sum(int(a) * int(a) for a in xi)
    q = Fraction(num, den); return float(w[i]), q

if __name__ == '__main__':
    import multiprocessing as mp
    import phase7_local as P
    mmax = int(sys.argv[1]) if len(sys.argv) > 1 else 4; nproc = int(sys.argv[2]) if len(sys.argv) > 2 else 6
    T = types_sorted(); idx = {t: i for i, t in enumerate(T)}
    phi = {i: [idx[k] for k in P.Phi_r(t, P.LODD[1])] for i, t in enumerate(T)}            # child c's 1-star type, c = 0..7
    fixed = {i: [c for c in range(8) if phi[i][c] == i] for i in phi}
    out = {'types': len(T), 'tiles_per_type': [len(t) for t in T], 'phi': phi, 'self_loops': {str(i): v for i, v in fixed.items() if v}, 'U': {}}
    log(f"Phi self-loops (tau = 1-star of its own child c): {out['self_loops']}")
    with mp.Pool(nproc) as pool:
        for m in range(1, mmax + 1):
            t0 = time.time(); res = pool.map(patch_bottom, [(j, m) for j in range(len(T))], chunksize=1)
            vals = {j: e for j, _, e, _ in res}; sizes = {j: n for j, _, _, n in res}; order = sorted(vals, key=vals.get)
            out['U'][m] = {'per_type': {str(j): vals[j] for j in vals}, 'tiles': {str(j): sizes[j] for j in sizes}, 'argmin': order[:5], 'min': vals[order[0]]}
            log(f"m={m}: U_m = {vals[order[0]]:.7f} at types {order[:5]} (values {[round(vals[j], 6) for j in order[:5]]}); patch tiles {min(sizes.values())}-{max(sizes.values())} ({time.time()-t0:.0f}s)")
            json.dump(out, open(os.path.join(RES, 'phase8_patch_bounds.json'), 'w'), indent=1)
    j = out['U'][mmax]['argmin'][0]; lam, q = certify(j, mmax)
    out['certificate'] = {'type': j, 'm': mmax, 'lambda_float': lam, 'rayleigh_upper_exact': f'{q.numerator}/{q.denominator}', 'rayleigh_upper': float(q)}
    log(f"certificate: E_* <= {float(q):.10f} (type {j}, m = {mmax}; float {lam:.10f})")
    json.dump(out, open(os.path.join(RES, 'phase8_patch_bounds.json'), 'w'), indent=1)
