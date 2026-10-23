#!/usr/bin/env python3
"""Phase VII-B (F): pre-registered scale observable on matched systems.

Observable (defined before any level-6 control value was computed): the finite-size approach ratio
    r_L = (Y_{L-1} - Y_L) / (Y_{L-2} - Y_{L-1}),   Y_L = lambda_min of the pinned operator on the level-L supertile,
for hull-covariant connections on the common chair geometry.  Y_L decreases in L (compression).  A bulk ground state with
quadratic dispersion confined to a box of side 2^(L+1) gives Y_L - E ~ C 4^(-L), i.e. r_L -> 1/4; r_L < 1/4 means faster
(localisation-type) convergence.  Matched systems: trivial, Z2 reflection-only, FR30 and its Abelian shadows chi_1, chi_2
(chi_3 equals chi_1 at every level computed).  FR30 levels 6-7 come from Phase V-E (phase5e_level7_evaluation.json);
FR30 level 6 is recomputed here as a cross-check.  Level-6 values carry exact Rayleigh upper certificates.
Usage: python -u -I audit/phase7b_scaling.py -> audit/results/phase7b_scaling.json"""
import os, sys, json, time
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); RES = os.path.join(HERE, 'results')
import numpy as np, scipy.sparse as sps, scipy.sparse.linalg as sla
import phase7_adversarial as A
from phase7b_controls import geometry, panels, link_field, CHI
from phase7_abelian_check import rayleigh_upper, REFLECTION_ONLY
from independent_clifford_q8_audit import FR30
T0 = time.time()
def log(*a): print(f"[{time.time()-T0:6.0f}s]", *a, flush=True)
MAT = np.array(A.MAT)

def operator_fast(n, pan, links, chi=None):
    a = np.concatenate([p[0] for p in pan]); b = np.concatenate([p[1] for p in pan]); L = np.concatenate(links)
    M = MAT[L] if chi is None else CHI[chi][L][:, None, None] * np.eye(2)[None]
    rows, cols, vals = [], [], []
    for i in range(2):
        for j in range(2):
            v = M[:, i, j]; nz = np.abs(v) > 0.5
            rows += [2 * a[nz] + i, 2 * b[nz] + j]; cols += [2 * b[nz] + j, 2 * a[nz] + i]; vals += [-v[nz], -np.conj(v[nz])]
    d = np.arange(2 * n); rows.append(d); cols.append(d); vals.append(np.full(2 * n, 24.0 + 0j))
    r = np.concatenate(rows); c = np.concatenate(cols); v = np.concatenate(vals)
    Re = sps.csr_matrix((np.rint(v.real).astype(np.int64), (r, c)), shape=(2 * n, 2 * n)); Im = sps.csr_matrix((np.rint(v.imag).astype(np.int64), (r, c)), shape=(2 * n, 2 * n))
    assert (Re != Re.T).nnz == 0 and (Im + Im.T).nnz == 0
    return Re, Im


def scalar_operator(n, pan, links, chi):
    """for +-1 links: the n x n real symmetric H_s with 24 on the diagonal and -sign(U_f) per panel (H = H_s (x) I_2)"""
    a = np.concatenate([p[0] for p in pan]); b = np.concatenate([p[1] for p in pan]); L = np.concatenate(links)
    if chi is not None: sg = CHI[chi][L]
    else:
        assert set(np.unique(L).tolist()) <= {0, 1}; sg = np.where(L == 0, 1, -1)
    r = np.concatenate([a, b, np.arange(n)]); c = np.concatenate([b, a, np.arange(n)]); v = np.concatenate([-sg, -sg, np.full(n, 24)])
    return sps.csr_matrix((v.astype(np.int64), (r, c)), shape=(n, n))

def rayleigh_scalar(Hs, scale=2 ** 20):
    from fractions import Fraction
    w, V = sla.eigsh(Hs.astype(float), k=2, which='SA', ncv=64, tol=1e-11); i = int(np.argmin(w)); v = V[:, i] / np.abs(V[:, i]).max()
    x = np.rint(v * scale).astype(np.int64); y = Hs @ x
    return float(w[i]), Fraction(sum(int(p) * int(q) for p, q in zip(x, y)), sum(int(p) * int(p) for p in x))

def rayleigh_big(Re, Im, scale=2 ** 20):
    from fractions import Fraction
    H = (Re + 1j * Im).astype(complex); w, V = sla.eigsh(H, k=2, which='SA', ncv=64, tol=1e-11); i = int(np.argmin(w)); v = V[:, i] / np.abs(V[:, i]).max()
    xr = np.rint(v.real * scale).astype(np.int64); xi = np.rint(v.imag * scale).astype(np.int64)
    yr = Re @ xr - Im @ xi; yi = Re @ xi + Im @ xr
    num = sum(int(a) * int(b) for a, b in zip(xr, yr)) + sum(int(a) * int(b) for a, b in zip(xi, yi)); den = sum(int(a) * int(a) for a in xr) + sum(int(a) * int(a) for a in xi)
    return float(w[i]), Fraction(num, den)

if __name__ == '__main__':
    out = {}; L = 6
    Gf, Tf, gridf, fidf = geometry(FR30, L); Gr, Tr, gridr, fidr = geometry(REFLECTION_ONLY, L); n = len(Gf)
    panF = panels(gridf); panR = panels(gridr); log(f"level {L}: {n} tiles, {sum(len(p[0]) for p in panF)} panels")
    sys_ = {'trivial': (panF, link_field(fidf, panF, 'trivial'), None), 'Z2_reflect': (panR, link_field(fidr, panR, 'clifford'), None),
            'FR30_chi1': (panF, link_field(fidf, panF, 'clifford'), 1), 'FR30_chi2': (panF, link_field(fidf, panF, 'clifford'), 2),
            'FR30': (panF, link_field(fidf, panF, 'clifford'), None)}
    prev = json.load(open(os.path.join(RES, 'phase7b_scaling.json'))) if os.path.exists(os.path.join(RES, 'phase7b_scaling.json')) else {}
    for name, (pan, links, chi) in sys_.items():
        if name in prev and 'rayleigh_upper_exact' in prev[name]: out[name] = prev[name]; log(f"L{L} {name}: reused {prev[name]['lambda_min']:.9f}"); continue
        t0 = time.time()
        if name == 'FR30':
            Re, Im = operator_fast(n, pan, links, chi); lam, q = rayleigh_big(Re, Im); how = 'complex 2n, eigsh ncv=64'
        else:
            Hs = scalar_operator(n, pan, links, chi); lam, q = rayleigh_scalar(Hs); how = 'scalar real n (links +-1: H = H_s (x) I_2), eigsh ncv=64'
        out[name] = {'level': L, 'lambda_min': lam, 'rayleigh_upper_exact': f'{q.numerator}/{q.denominator}', 'rayleigh_upper': float(q), 'seconds': time.time() - t0, 'method': how}
        log(f"L{L} {name}: lambda_min {lam:.9f}; exact Rayleigh <= {float(q):.10f} ({time.time()-t0:.0f}s, {how})")
        json.dump(out, open(os.path.join(RES, 'phase7b_scaling.json'), 'w'), indent=1)
    # assemble Y_L sequences and ratios
    ctl = json.load(open(os.path.join(RES, 'phase7b_controls.json'))); ab = json.load(open(os.path.join(RES, 'phase7_abelian_check.json')))
    ev = json.load(open(os.path.join(RES, 'phase5e_level7_evaluation.json'))); E7 = ev['E7']; E6 = E7 + ev['d7']
    seq = {'trivial': [ab['trivial'][str(l)]['lambda_min_float'] for l in (2, 3, 4, 5)] + [out['trivial']['lambda_min']],
           'Z2_reflect': [ab['reflection_only_Z2'][str(l)]['lambda_min_float'] for l in (2, 3, 4, 5)] + [out['Z2_reflect']['lambda_min']],
           'FR30': [ab['fr30'][str(l)]['lambda_min_float'] for l in (2, 3, 4, 5)] + [E6, E7]}
    for k in (1, 2): seq[f'FR30_chi{k}'] = [None] + [ctl[f'FR30_chi{k}'][str(l)]['lambda_min'] for l in (3, 4, 5)] + [out[f'FR30_chi{k}']['lambda_min']]
    ratios = {}
    for name, ys in seq.items():
        r = {}
        for i in range(2, len(ys)):
            if ys[i - 2] is None: continue
            r[str(i + 2)] = (ys[i - 1] - ys[i]) / (ys[i - 2] - ys[i - 1])
        ratios[name] = r
    out['Y_sequences_from_L2'] = seq; out['r_L'] = ratios; out['fr30_E6_check'] = {'recomputed': out['FR30']['lambda_min'], 'phase5e': E6}
    log(f"ratios r_L: {json.dumps(ratios)}")
    json.dump(out, open(os.path.join(RES, 'phase7b_scaling.json'), 'w'), indent=1)
