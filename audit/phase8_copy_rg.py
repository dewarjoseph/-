#!/usr/bin/env python3
"""Phase VIII (sections 4/5): the renormalized edge problem on the lattice of level-k copies, with a fixed local fiber.

Exact reduction (Theorem E1 of Phase V-E, any partition with block-diagonal interior).  Split the pinned level-L supertile into
its 8^(L-k) depth-(L-k) copies of T_k.  Every copy's pinned operator equals T_k's in the copy's own (canonical) tile order,
because links depend only on relative frames (Theorem D0); hence every copy has the SAME surface response
    R_k(E) = H_SS - E - B^+ diag(1/(l - E)) B        (pole form; H_II = Q diag(l) Q^+, B = Q^+ H_IS)
and the Schur complement of H(T_L) - E onto the union of copy surfaces is  K_L(E) = I (x) R_k(E) + Off_L,  with Off_L the
inter-copy panel hoppings.  lambda_min H(T_L) is the unique root of lambda_min K_L(E) below lambda_II(T_k).

Renormalized state.  A FIXED subspace U (dim d) of the T_k surface space, used in every copy (gauge-covariant: one subspace in
the copies' common substitution frame, Kramers-complete when U is built from Kramers-closed data).  Galerkin/Ritz:
    M_W(E) = I (x) m(E) + Off_W,   m(E) = U^+ R_k(E) U  (d x d, identical for all copies),   (Off_W)_{jj'} = U^+ Off_{jj'} U.
g(E) = lambda_min M_W(E) is concave and decreasing with slope <= -1; its root E_W >= lambda_min H(T_L) (Theorem E3).  M_W is
block-sparse (copies couple only across shared panels), so the problem scales to level 7 (4096 copies).

Fibers: 'env' = built from the 72 legal 1-star environment patches sigma^k(tau) only (audit/phase8_env_fiber.py; no level >= 5
data); 'deep67' = V-E's subspace trained on the level-6/7 ground pairs (reference; in-sample at levels 6, 7).
Usage: python -u -I audit/phase8_copy_rg.py L d fiber -> appends to audit/results/phase8_copy_rg.jsonl"""
import os, sys, json, time
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); RES = os.path.join(HERE, 'results')
import numpy as np, scipy.sparse as sps, scipy.sparse.linalg as sla
import phase5e_rg as rg
import phase5d_schur as d
import phase7_local as P
from independent_clifford_q8_audit import FR30
T0 = time.time()
def log(*a): print(f"[{time.time()-T0:7.0f}s]", *a, flush=True)
EXACT = {4: 8.919634360169246, 5: 8.797011314651467, 6: 8.77013362902455, 7: 8.764911988377174}
FIBER_CACHE = os.path.join(RES, 'phase8_fibers_k3.npz')

def copy_data(k):
    tiles = d.tiles_of(FR30, k); H, edges = d.build(tiles); n = len(tiles); deg = d.degrees(n, edges)
    S = np.nonzero(deg < 24)[0]; I = np.nonzero(deg == 24)[0]; ss, ii = d.spinor(S), d.spinor(I); H = H.tocsr()
    HII = H[ii][:, ii].toarray(); l, Q = np.linalg.eigh(HII)
    return {'S': S, 'pos': {int(t): p for p, t in enumerate(S)}, 'HSS': H[ss][:, ss].toarray(), 'B': Q.conj().T @ H[ii][:, ss].toarray(), 'l': l}

def fibers():
    if os.path.exists(FIBER_CACHE):
        z = np.load(FIBER_CACHE); return {'env': z['env'], 'deep67': z['deep67']}
    import phase5e_run as run
    from phase8_env_fiber import env_snapshots
    from phase7b_local_rules import legal_V1
    V1, _ = legal_V1(); Xenv, _, surf_k = env_snapshots(V1, 8)
    Uenv, _, _ = np.linalg.svd(Xenv, full_matrices=False)
    vecs = run.fr30_vectors(); Xs = {}
    for L in (6, 7):
        v = np.asarray(vecs[L], complex); v = v / np.linalg.norm(v); Y = run.snapshots(v, L, 3, surf_k); Xs[L] = Y / np.linalg.norm(Y)
    U67, _, _ = np.linalg.svd(np.hstack([Xs[6], Xs[7]]), full_matrices=False)
    np.savez(FIBER_CACHE, env=Uenv[:, :300], deep67=U67[:, :300]); return {'env': Uenv[:, :300], 'deep67': U67[:, :300]}

def coupling(L, k, cd, U):
    """block-sparse Off_W: for every ordered pair of adjacent copies (j, j'), U^+ Off_{jj'} U, from the panel list of T_L
    (fiber rows are gathered one block at a time, so level 7 fits in memory)."""
    from phase7b_controls import geometry, panels
    G, T, grid, _ = geometry(FR30, L); fid = P.frame_index(G); pan = panels(grid); nk = 8 ** k; dd = U.shape[1]
    a = np.concatenate([p[0] for p in pan]); b = np.concatenate([p[1] for p in pan]); ax = np.concatenate([p[2] for p in pan]); del pan, grid
    ja, jb = a // nk, b // nk; m = ja != jb; a, b, ax, ja, jb = a[m], b[m], ax[m], ja[m], jb[m]
    pos = np.full(nk, -1); pos[cd['S']] = np.arange(len(cd['S'])); pa, pb = pos[a % nk], pos[b % nk]
    assert (pa >= 0).all() and (pb >= 0).all()                                     # inter-copy panels join surface tiles
    order = np.lexsort((jb, ja)); a, b, ax, ja, jb, pa, pb = (x[order] for x in (a, b, ax, ja, jb, pa, pb))
    U2 = U.reshape(-1, 2, dd); blocks = {}
    cut = np.flatnonzero(np.r_[True, (ja[1:] != ja[:-1]) | (jb[1:] != jb[:-1]), True])
    for s, e in zip(cut[:-1], cut[1:]):
        C = P.LINKGI[fid[a[s:e]], fid[b[s:e]], ax[s:e]]; C = C[..., 0] + 1j * C[..., 1]   # link a -> b (2x2)
        X = np.einsum('mij,mjd->mid', -C, U2[pb[s:e]]).reshape(-1, dd); Y = U2[pa[s:e]].reshape(-1, dd)
        blk = Y.conj().T @ X; j, jp = int(ja[s]), int(jb[s])
        blocks[(j, jp)] = blocks.get((j, jp), 0) + blk; blocks[(jp, j)] = blocks.get((jp, j), 0) + blk.conj().T
    return blocks, 8 ** (L - k)

def assemble(blocks, ncopy, dd):
    """the coupling blocks as one block-sparse (BSR) matrix"""
    keys = sorted(blocks); rows = np.array([j for j, _ in keys]); cols = np.array([jp for _, jp in keys])
    data = np.stack([blocks[key] for key in keys]); indptr = np.searchsorted(rows, np.arange(ncopy + 1))
    return sps.bsr_matrix((data, cols, indptr), shape=(ncopy * dd, ncopy * dd))

def solve(L, dd, name, k=3, write=True):
    cd = copy_data(k); U = fibers()[name][:, :dd]; U, _ = np.linalg.qr(U)
    t0 = time.time(); blocks, ncopy = coupling(L, k, cd, U); nblk = len(blocks); Off = assemble(blocks, ncopy, dd); del blocks
    log(f"L{L} {name} d={dd}: {ncopy} copies, {nblk} coupling blocks, dim {ncopy*dd} ({time.time()-t0:.0f}s)")
    A0 = U.conj().T @ cd['HSS'] @ U; CB = cd['B'] @ U; lII = float(cd['l'][0])
    def mE(E): return A0 - E * np.eye(dd) - (CB.conj().T * (1.0 / (cd['l'] - E))) @ CB
    def dm(E): return -np.eye(dd) - (CB.conj().T * (1.0 / (cd['l'] - E) ** 2)) @ CB
    SHIFT = 10.0                                                          # ARPACK's tol is relative: keep eigenvalues away from 0
    last = {}                                                             # previous eigenvector: the starting vector of the next solve
    def g(E, vec=False):
        A = mE(E) + SHIFT * np.eye(dd)                                    # M = I (x) A + Off, applied without forming I (x) A
        def mv(x): x = np.ravel(x); return (x.reshape(ncopy, dd) @ A.T).ravel() + Off @ x
        M = sla.LinearOperator((ncopy * dd, ncopy * dd), matvec=mv, dtype=complex)
        w, V = sla.eigsh(M, k=1, which='SA', tol=1e-11, ncv=64, maxiter=100000, v0=last.get('x')); x = V[:, 0]; w = w - SHIFT; last['x'] = x
        if not vec: return float(w[0])
        X = x.reshape(ncopy, dd); slope = float(np.real(np.einsum('jd,de,je->', X.conj(), dm(E), X)))
        return float(w[0]), slope
    # bracketed Newton/chord on the concave decreasing g, starting right of the expected root
    lo, hi = EXACT.get(L, 8.7) - 0.05, min(lII - 1e-6, EXACT.get(L, 8.7) + 1.0); glo = g(lo); ghi = g(hi)
    while glo < 0: lo -= 0.2; glo = g(lo)
    E = hi; it = 0
    while it < 40:
        it += 1; val, sl = g(E, vec=True)
        if abs(val) < 1e-11: break
        if val > 0: lo, glo = E, val
        else: hi, ghi = E, val
        En = E - val / sl
        if not (lo < En < hi): En = lo - glo * (hi - lo) / (ghi - glo)
        if abs(En - E) < 1e-12: E = En; break
        E = En
    rec = {'L': L, 'k': k, 'fiber': name, 'd': dd, 'copies': ncopy, 'dim': ncopy * dd, 'E_W': E, 'exact': EXACT.get(L), 'err': (E - EXACT[L]) if L in EXACT else None,
           'iterations': it, 'seconds': time.time() - t0, 'impl': 'bsr-linop'}
    log(f"L{L} {name} d={dd}: E_W = {E:.8f}  exact {EXACT.get(L)}  err {rec['err']}  ({it} it, {rec['seconds']:.0f}s)")
    if write:
        with open(os.path.join(RES, 'phase8_copy_rg.jsonl'), 'a') as f: f.write(json.dumps(rec) + '\n')
    return rec

if __name__ == '__main__':
    L, dd, name = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
    solve(L, dd, name)
