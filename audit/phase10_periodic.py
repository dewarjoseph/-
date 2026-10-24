#!/usr/bin/env python3
"""Phase X: periodic chair approximants -- the mandatory periodic control on the Chair44 geometry itself.

The level-k supertile T_k of any decoration occupies the chair scaled by 2^k, and the chair tiles Z^3 by the translations of
Lambda_7 = {x : x1 + 2 x2 + 4 x3 = 0 mod 7} (PHASE5A framework, s.5.1 item 4).  So the translates of T_k by 2^k Lambda_7 form a
periodic tiling by chairs with proper frames: every copy carries the rule's T_k, but the seams between copies are not
hierarchical (they are, in general, illegal patterns of the hull).  On that tiling Deg = 24 and H = 24 - A_U exactly, and its
floor is E_per,k = min_theta lambda_min H(theta), H(theta) the Bloch matrix on T_k (basis b1 = (1,1,1), b2 = (2,-1,0),
b3 = (0,2,-1) of Lambda_7, det = 7).  E_per,k is an exact infinite-volume quantity (up to the minimisation over theta).
Usage: python -u -I audit/phase10_periodic.py <class> [k ...] -> appends to audit/results/phase10_periodic.jsonl"""
import os, sys, json, time, math, itertools, types
sys.modules.setdefault('resource', types.SimpleNamespace(getrusage=lambda *a: types.SimpleNamespace(ru_maxrss=0), RUSAGE_SELF=0))
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); RES = os.path.join(HERE, 'results')
import numpy as np, scipy.sparse as sps, scipy.sparse.linalg as sla
import phase9_pair as P9
T0 = time.time()
def log(*a): print(f"[{time.time()-T0:7.0f}s]", *a, flush=True)
BASIS = np.array([[1, 1, 1], [2, -1, 0], [0, 2, -1]])

class Periodic:
    def __init__(self, dec, k):
        S = P9.build([dec] * k); self.S = S; self.n = S['n']; grid = S['grid']; N = grid.shape[0]; B = (2 ** k) * BASIS
        G = S['G']; rows = []                                                # (a, b, axis, n_vec) for every panel a -> b crossing +e_axis
        owned = np.argwhere(grid >= 0)
        combos = [np.array(c) for c in itertools.product(range(-2, 3), repeat=3)]
        for q in owned:
            a = grid[tuple(q)]
            for ax in range(3):
                q2 = q.copy(); q2[ax] += 1
                if (q2 < N).all() and grid[tuple(q2)] >= 0:
                    b = grid[tuple(q2)]
                    if b != a: rows.append((a, b, ax, (0, 0, 0)))
                    continue
                for c in combos:                                             # the translate containing q2
                    q3 = q2 - c @ B
                    if (q3 >= 0).all() and (q3 < N).all() and grid[tuple(q3)] >= 0:
                        rows.append((a, grid[tuple(q3)], ax, tuple(int(x) for x in c))); break
                else: raise RuntimeError('no translate found')
        R = np.array([(a, b, ax) for a, b, ax, _ in rows]); self.nv = np.array([nv for *_, nv in rows])
        self.U = P9.links(G, R[:, 0], R[:, 1], R[:, 2]); self.a, self.b = R[:, 0], R[:, 1]
        deg = np.bincount(self.a, minlength=self.n) + np.bincount(self.b, minlength=self.n); assert (deg == 24).all(), 'periodic tiling must have degree 24'
    def H(self, theta):
        ph = np.exp(1j * (self.nv @ np.asarray(theta, float))); Us = self.U * ph[:, None, None]; a, b, n = self.a, self.b, self.n
        r = np.concatenate([2 * a[:, None] + np.array([0, 0, 1, 1]), 2 * b[:, None] + np.array([0, 0, 1, 1])]).ravel()
        c = np.concatenate([2 * b[:, None] + np.array([0, 1, 0, 1]), 2 * a[:, None] + np.array([0, 1, 0, 1])]).ravel()
        v = np.concatenate([Us.reshape(-1, 4), np.conj(np.transpose(Us, (0, 2, 1))).reshape(-1, 4)]).ravel()
        return (24 * sps.identity(2 * n) - sps.csr_matrix((v, (r, c)), shape=(2 * n, 2 * n))).tocsr()
    def lam(self, theta):
        H = self.H(theta)
        if H.shape[0] <= 2048: return float(np.linalg.eigvalsh(H.toarray())[0])
        return float(sla.eigsh(H, k=2, which='SA', tol=1e-10, ncv=40, return_eigenvectors=False).min())
    def floor(self, grid=4):
        from scipy.optimize import minimize
        ts = [2 * math.pi * i / grid for i in range(grid)]; vals = sorted((self.lam(t), t) for t in itertools.product(ts, repeat=3))
        best, arg = vals[0][0], np.array(vals[0][1])
        for v, t in vals[:3]:
            r = minimize(lambda th: self.lam(th), np.array(t), method='Nelder-Mead', options={'xatol': 1e-6, 'fatol': 1e-10, 'maxiter': 600})
            if r.fun < best: best, arg = float(r.fun), r.x
        return best, arg, vals[0][0]

if __name__ == '__main__':
    cls = int(sys.argv[1]); ks = [int(x) for x in sys.argv[2:]] or [2, 3]
    for k in ks:
        t0 = time.time(); per = Periodic(P9.decoration(cls), k); E, th, grid_min = per.floor(grid=4 if k <= 3 else 3)
        rec = {'class': cls, 'k': k, 'tiles_per_cell': per.n, 'E_per': E, 'theta': list(map(float, th)), 'grid_min': grid_min, 'seconds': time.time() - t0}
        log(rec)
        with open(os.path.join(RES, 'phase10_periodic.jsonl'), 'a') as f: f.write(json.dumps(rec) + '\n')
