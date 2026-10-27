#!/usr/bin/env python3
"""Phase XII, the frozen next experiment: exact level-L upper bounds Y_L (pinned T_L) for the frontier rules, L up to 7.

The operator is exactly Phase XI's (phase11_frontier.Level.H, i.e. phase11_chair.hermitian): on the tiles of T_L,
    H = 24 - sum over panels (U(a->b) e_a e_b^+ + h.c.),  U(a->b) = (sigma . M_a^T e_k)(sigma . M_b^T e_k)  (2x2, Pauli),
with the panels (a, b, k) of phase11_chair.Patch.  Only the assembly is leaner, so that T_7 (2 097 152 tiles, complex dimension
4 194 304) fits in memory: each link is a signed Pauli product s * sigma_p sigma_q, coded by its 2x2 entries as small Gaussian
integers; the panels between the same two tiles are summed before the sparse matrix is built, and no per-panel complex matrix
is ever stored.  The bottom is found by ARPACK (eigsh, which='SA', tol 1e-10, as Phase XI); the bound is the exact rational
Rayleigh quotient of the integer rounding of the eigenvector (phase11_frontier.exact_upper), an upper bound on E_* whatever the
accuracy of the eigenvector.
Usage: python -u -I audit/phase12_y7.py <L> <j> ...   (j = extended index)  -> audit/results/phase12_y7.jsonl (one record per run)"""
import os, sys, json, time, types, gc
sys.modules.setdefault('resource', types.SimpleNamespace(getrusage=lambda *a: types.SimpleNamespace(ru_maxrss=0), RUSAGE_SELF=0))
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); RES = os.path.join(HERE, 'results')
import numpy as np, scipy.sparse as sps, scipy.sparse.linalg as sla
import phase11_chair as C, phase11_frontier as F
OUT = os.path.join(RES, 'phase12_y7.jsonl'); T0 = time.time()
def log(*a): print(f'[{time.time() - T0:7.0f}s]', *a, flush=True)

# 2x2 entries of sigma_p sigma_q as Gaussian integers (re, im): PAULI[p] @ PAULI[q]
SS = np.einsum('pij,qjk->pqik', C.PAULI, C.PAULI)
SS_RE = np.rint(SS.real).astype(np.int8); SS_IM = np.rint(SS.imag).astype(np.int8)
assert np.array_equal(SS, SS_RE + 1j * SS_IM)

def geometry(L):
    """tiles of T_L in centroid order (decoration-independent), panels (a, b, k) as int32/int8"""
    lev = F.Level.__new__(F.Level); lev.L = L
    G, T = C.supertile(C.extended_decoration(0), L); X = C.centroid14(G, T); lev.K = 14 * 2 ** (L + 3)
    o = np.argsort(lev.key(X)); G, T = G[o], T[o]; lev.keys = lev.key(C.centroid14(G, T)); lev.n = len(G); del X
    a, b, k = C.Patch(G, T).panels(); del G, T; gc.collect()
    lev.a, lev.b, lev.k = a.astype(np.int32), b.astype(np.int32), k.astype(np.int8)
    return lev

def operator(lev, dec):
    """the complex sparse H of Phase XI for decoration dec, assembled with tile pairs merged"""
    G = lev.frames(dec); n = lev.n
    R = G[lev.a.astype(np.int64), lev.k.astype(np.int64), :]; p = np.abs(R).argmax(1); sa = R[np.arange(len(R)), p]; del R
    R = G[lev.b.astype(np.int64), lev.k.astype(np.int64), :]; q = np.abs(R).argmax(1); sb = R[np.arange(len(R)), q]; del R, G
    s = (sa * sb).astype(np.int8); del sa, sb
    a, b = lev.a, lev.b
    swap = a > b                                    # orient every panel as (min, max); U(b -> a) = U(a -> b)^+
    lo = np.where(swap, b, a).astype(np.int64); hi = np.where(swap, a, b).astype(np.int64)
    key = lo * n + hi; o = np.argsort(key, kind='stable'); key = key[o]
    p, q, s, swap = p[o], q[o], s[o], swap[o]; del o
    re = SS_RE[p, q].astype(np.int16) * s[:, None, None]; im = SS_IM[p, q].astype(np.int16) * s[:, None, None]; del p, q, s
    # adjoint where swapped: (re + i im)^+ -> transpose, conjugate
    re[swap] = np.transpose(re[swap], (0, 2, 1)); im[swap] = -np.transpose(im[swap], (0, 2, 1)); del swap
    start = np.flatnonzero(np.r_[True, key[1:] != key[:-1]]); pk = key[start]; del key
    Re = np.add.reduceat(re.reshape(-1, 4), start, axis=0); Im = np.add.reduceat(im.reshape(-1, 4), start, axis=0); del re, im
    pa = (pk // n).astype(np.int64); pb = (pk % n).astype(np.int64); del pk
    V = (Re + 1j * Im).astype(np.complex128); del Re, Im
    nz = V != 0                                     # cancellations between panels of one tile pair
    ii, jj = np.array([0, 0, 1, 1]), np.array([0, 1, 0, 1])
    r1 = (2 * pa[:, None] + ii)[nz]; c1 = (2 * pb[:, None] + jj)[nz]; v1 = -V[nz]
    r2 = (2 * pb[:, None] + jj)[nz]; c2 = (2 * pa[:, None] + ii)[nz]; v2 = -np.conj(V[nz]); del V, nz, pa, pb
    d = np.arange(2 * n, dtype=np.int64)
    rows = np.concatenate([r1, r2, d]).astype(np.int32); cols = np.concatenate([c1, c2, d]).astype(np.int32); del r1, r2, c1, c2
    vals = np.concatenate([v1, v2, np.full(2 * n, 24.0 + 0j)]); del v1, v2, d; gc.collect()
    H = sps.csr_matrix((vals, (rows, cols)), shape=(2 * n, 2 * n)); del rows, cols, vals; gc.collect()
    H.sum_duplicates(); return H

def exact_upper(H, v, chunk=1 << 18):
    """phase11_frontier.exact_upper (the same integer rounding of v, the same exact rational), computed by row chunks so that no
    integer copy of the whole matrix is held"""
    v = v / np.abs(v).max(); s = 2 ** 20
    xr = np.rint(v.real * s).astype(np.int64); xi = np.rint(v.imag * s).astype(np.int64)
    num = den = 0
    for r0 in range(0, H.shape[0], chunk):
        Hc = H[r0:r0 + chunk]; Hr = Hc.real; Hi = Hc.imag
        assert np.array_equal(Hr.data, np.rint(Hr.data)) and np.array_equal(Hi.data, np.rint(Hi.data))
        Hr = Hr.astype(np.int64); Hi = Hi.astype(np.int64)
        yr = Hr @ xr - Hi @ xi; yi = Hr @ xi + Hi @ xr                     # |entries| <= 48 * 2^20: no int64 overflow
        sl = slice(r0, r0 + chunk)
        num += int(np.sum((xr[sl] * yr).astype(object))) + int(np.sum((xi[sl] * yi).astype(object)))
    den = int(np.sum((xr * xr).astype(object))) + int(np.sum((xi * xi).astype(object)))
    return num, den

def run(L, j, lev=None):
    t0 = time.time(); lev = lev or geometry(L); log(f'L={L} j={j}: geometry {lev.n} tiles, {len(lev.a)} panels')
    H = operator(lev, C.extended_decoration(j)); log(f'  operator {H.shape[0]} x {H.shape[0]}, nnz {H.nnz} [{time.time() - t0:.0f}s]')
    assert abs(H - H.getH()).max() == 0
    t1 = time.time(); lam, v = F.lowest(H); t_eig = time.time() - t1
    res = float(np.linalg.norm(H @ v - lam * v)); log(f'  eigsh {lam!r}, residual {res:.2e} [{t_eig:.0f}s]')
    num, den = exact_upper(H, v)
    rec = {'j': j, 'L': L, 'tiles': lev.n, 'nnz': int(H.nnz), 'float': lam, 'residual': res, 'upper_num': str(num), 'upper_den': str(den),
           'upper': num / den, 'seconds': time.time() - t0, 'seconds_eigsh': t_eig}
    with open(OUT, 'a') as f: f.write(json.dumps(rec) + '\n')
    log(f'  exact upper {num / den!r} [{time.time() - t0:.0f}s]'); return rec

if __name__ == '__main__':
    os.environ.setdefault('OMP_NUM_THREADS', '1')
    L = int(sys.argv[1]); lev = geometry(L)
    for j in map(int, sys.argv[2:]): run(L, j, lev); gc.collect()
