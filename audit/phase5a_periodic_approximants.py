"""
Phase 5a / Task B2a (extension): PERIODIC APPROXIMANTS OF THE FR30 CHAIR TILING BY EXACT BLOCH THEORY.

The level-k FR30 supertile (a chair of side 2^(k+1) made of 8^k unit chairs with their true FR30 frames) is repeated
by the translations of 2^k * Lambda_7 (src/chair44/periodic_crystal.py, "rotated-cell periodic control").  This is a
genuine periodic tiling of R^3 by unit chairs: every chair has 24 shared panels, the Q8 link rule is applied with the
true geometric frames, and the only non-FR30 feature is the way neighbouring supertile copies meet (a fraction
~2^-k of the tiles touch such an interface).  The pinned operator 24 - A is therefore periodic with 8^k chairs per
cell and its spectrum is the union over the Brillouin zone of the (2*8^k)-dimensional Bloch matrices.

Run from the repository root:  python3 -u -I audit/phase5a_periodic_approximants.py [kmax]
"""
import os, sys, time, itertools, collections
for _v in ('OPENBLAS_NUM_THREADS', 'OMP_NUM_THREADS', 'MKL_NUM_THREADS'): os.environ.setdefault(_v, '1')
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
import scipy.optimize as sopt, scipy.sparse as sps, scipy.sparse.linalg as spl
from independent_clifford_q8_audit import FR30, U3, tiles_at_level, panel_edges, clifford_link, q8label
from phase5a_periodic_control import B, owner_of_cube, phi, hessian_fd

T0 = time.time()
def log(*a): print(*a, flush=True)

class Approximant:
    def __init__(self, k):
        self.k = k; self.N = 2 ** k                                   # supertile side 2N = 2^(k+1); lattice 2^k Lambda_7
        self.tiles = tiles_at_level(FR30, k); self.n = len(self.tiles)
        self.owner, self.edges = panel_edges(self.tiles)
        self.Bp = self.N * B                                          # rows = basis of the period lattice (ambient)
        hops = []; self.interface = np.zeros(self.n, dtype=bool)
        cubes_of = collections.defaultdict(list)
        for c, a in self.owner.items(): cubes_of[a].append(c)
        for a in range(self.n):
            Ma = self.tiles[a][0]; cnt = 0
            for c in cubes_of[a]:
                for ax in range(3):
                    for s in (1, -1):
                        c2 = np.array(c); c2[ax] += s; n = np.zeros(3, dtype=int); n[ax] = s
                        b = self.owner.get(tuple(c2)); d = np.zeros(3, dtype=int)
                        if b is None:
                            V = c2 // self.N                                  # big-cube index (floor division)
                            d = self.N * owner_of_cube(V)                     # translation of the supertile copy containing c2
                            b = self.owner[tuple(c2 - d)]
                        if b == a and not d.any(): continue                   # internal adjacency
                        hops.append((a, b, d, clifford_link(Ma, self.tiles[b][0], n)))
                        if d.any(): self.interface[a] = True
                        cnt += 1
            assert cnt == 24, (a, cnt)
        self.hops = hops
        self.D = np.array([d for _, _, d, _ in hops], dtype=float)
        self.rows = np.array([a for a, _, _, _ in hops]); self.cols = np.array([b for _, b, _, _ in hops])
        self.C = np.array([C for _, _, _, C in hops])                 # (F,2,2)
        self.dim = 2 * self.n
    def Hq(self, q, dense=True):
        ph = np.exp(1j * (self.D @ np.asarray(q, dtype=float)))
        vals = -(ph[:, None, None] * self.C)                           # (F,2,2)
        r = (2 * self.rows[:, None, None] + np.arange(2)[None, :, None] + 0 * np.arange(2)[None, None, :]).ravel()
        c = (2 * self.cols[:, None, None] + 0 * np.arange(2)[None, :, None] + np.arange(2)[None, None, :]).ravel()
        H = sps.coo_matrix((vals.ravel(), (r, c)), shape=(self.dim, self.dim)).tocsr()
        H = H + sps.identity(self.dim, dtype=complex, format='csr') * 24.0
        return H.toarray() if dense else H
    def lowest(self, q, nev=4):
        if self.dim <= 2048:
            return np.linalg.eigvalsh(self.Hq(q))[:nev]
        w = spl.eigsh(self.Hq(q, dense=False), k=nev, sigma=0.0, which='LM', return_eigenvectors=False)
        return np.sort(w)
    def lowest_vec(self, q):
        if self.dim <= 2048:
            w, V = np.linalg.eigh(self.Hq(q)); return w[:4], V[:, 0]
        w, V = spl.eigsh(self.Hq(q, dense=False), k=4, sigma=0.0, which='LM'); o = np.argsort(w); return w[o], V[:, o[0]]
    def q_of_theta(self, th): return 2 * np.pi * np.linalg.solve(self.Bp.astype(float), np.asarray(th, dtype=float))
    def theta_of_q(self, q): return (self.Bp @ np.asarray(q) / (2 * np.pi)) % 1.0
    def fg(self, q):
        """lowest eigenvalue and its Hellmann-Feynman gradient."""
        w, v = self.lowest_vec(q)
        ph = np.exp(1j * (self.D @ q))
        va = v.reshape(self.n, 2); M = np.einsum('fa,fab,fb->f', va[self.rows].conj(), self.C, va[self.cols])
        g = -np.real((1j * ph * M) @ self.D)
        return w[0], g
    def flux(self):
        """Exact Q8 class counts of all lattice-edge plaquettes of the torus (21 * 8^k plaquettes)."""
        cls = collections.Counter(); internal = 0; ntot = 0
        def tile_of(c):
            c = np.asarray(c); b = self.owner.get(tuple(c))
            if b is not None: return b, (0, 0, 0)
            V = c // self.N; d = self.N * owner_of_cube(V); return self.owner[tuple(c - d)], tuple(d)
        for c in self.owner:
            c = np.array(c)
            for (i, j) in [(0, 1), (1, 2), (0, 2)]:
                ei = np.eye(3, dtype=int)[i]; ej = np.eye(3, dtype=int)[j]
                ring = [c, c + ei, c + ei + ej, c + ej]; ids = [tile_of(cc) for cc in ring]; ntot += 1
                if len(set(ids)) == 1: internal += 1; continue
                W = np.eye(2, dtype=complex)
                for t in range(4):
                    if ids[t] == ids[(t + 1) % 4]: continue
                    W = W @ clifford_link(self.tiles[ids[t][0]][0], self.tiles[ids[(t + 1) % 4][0]][0], ring[(t + 1) % 4] - ring[t])
                cls[q8label(W)] += 1
        assert ntot == 21 * self.n and internal == 3 * self.n
        inter = ntot - internal
        by = {'1': cls['+1'], '-1': cls['-1'], 'i': cls['+i'] + cls['-i'], 'j': cls['+j'] + cls['-j'], 'k': cls['+k'] + cls['-k']}
        assert sum(by.values()) == inter and cls['other'] == 0
        return inter, by

def run(k, grid, budget):
    t0 = time.time(); ap = Approximant(k)
    log("=" * 100)
    log(f"LEVEL-{k} PERIODIC APPROXIMANT: {ap.n} chairs per cell, Bloch dimension {ap.dim}, period lattice 2^{k} Lambda_7, "
        f"{len(ap.hops)} oriented panels (= 24 per chair), interface tiles (touching another supertile copy): {ap.interface.sum()}/{ap.n} = {ap.interface.mean():.3f}  (build {time.time()-t0:.0f}s)")
    inter, cls = ap.flux()
    log(f" exact torus flux: inter-tile plaquettes {inter} (={inter/ap.n:.1f} per chair), classes {cls};  fractions: nontriv={1-cls['1']/inter:.5f} (FR30 limit 17/36={17/36:.5f}),"
        f" traceless={(cls['i']+cls['j']+cls['k'])/inter:.5f} (55/144={55/144:.5f}), -1={cls['-1']/inter:.5f} (13/144={13/144:.5f})  ({time.time()-t0:.0f}s)")
    # TRIMs first
    trims = list(itertools.product((0.0, 0.5), repeat=3))
    res = {}
    for th in trims:
        w = ap.lowest(ap.q_of_theta(th)); res[th] = w
    for th in trims: log(f"   theta={th}: lowest {np.round(res[th], 6).tolist()}")
    best_th = min(trims, key=lambda th: res[th][0]); E_trim = res[best_th][0]
    log(f" minimum over the 8 TRIMs: E={E_trim:.9f} at theta={best_th}  ({time.time()-t0:.0f}s)")
    # grid
    if grid > 2:
        ths = [th for th in itertools.product(np.arange(grid) / grid, repeat=3)]
        Eg = {}
        for th in ths:
            if time.time() - t0 > budget: log("   grid: time budget reached"); break
            Eg[th] = ap.lowest(ap.q_of_theta(th), nev=1)[0]
        bt = min(Eg, key=Eg.get)
        log(f" {grid}^3 grid ({len(Eg)} points evaluated): min E={Eg[bt]:.9f} at theta={np.round(bt,4).tolist()}, max of lowest band={max(Eg.values()):.6f}  ({time.time()-t0:.0f}s)")
        starts = sorted(Eg, key=Eg.get)[:2]
    else:
        starts = [best_th]
    # BFGS refinement with Hellmann-Feynman gradient
    best = (np.inf, None)
    for th in starts:
        if time.time() - t0 > budget: break
        q0 = ap.q_of_theta(th); cnt = [0]
        def fg(q): cnt[0] += 1; return ap.fg(q)
        r = sopt.minimize(fg, q0, jac=True, method='BFGS', options=dict(gtol=1e-8, maxiter=60))
        log(f"   BFGS from theta={np.round(th,4).tolist()}: E={r.fun:.9f} at theta={np.round(ap.theta_of_q(r.x),5).tolist()} |grad|={np.linalg.norm(r.jac):.1e} evals={cnt[0]} ({time.time()-t0:.0f}s)")
        if r.fun < best[0]: best = (r.fun, r.x)
    E, q = best if best[1] is not None else (E_trim, ap.q_of_theta(best_th))
    w, v = ap.lowest_vec(q)
    th = ap.theta_of_q(q); trim = all(min(abs(t), abs(t - .5), abs(t - 1)) < 2e-4 for t in th)
    wt = np.abs(v.reshape(ap.n, 2)) ** 2; wt = wt.sum(1); wt /= wt.sum()
    log(f" BAND BOTTOM E_per({k}) = {E:.9f} at theta={np.round(th,5).tolist()} ({'TRIM' if trim else 'generic'});  lowest four at the minimum {np.round(w[:4],7).tolist()} (gap12={w[1]-w[0]:.1e});"
        f"  ground-state tile IPR={np.sum(wt**2):.5f} (1/n={1/ap.n:.5f}), weight on interface tiles={wt[ap.interface].sum():.4f} (their fraction {ap.interface.mean():.3f})")
    wg = ap.lowest(q + np.array([0.11, -0.07, 0.05]) / ap.N, nev=2); log(f"   degeneracy of the lowest band at a generic q: gap12={wg[1]-wg[0]:.2e}")
    if ap.dim <= 2048 and time.time() - t0 < budget:
        hs = {h: hessian_fd(ap, q, h / ap.N) for h in (0.08, 0.04, 0.02)}
        R = (4 * hs[0.02] - hs[0.04]) / 3; R0 = (4 * hs[0.04] - hs[0.08]) / 3
        log(f" Hessian of the lowest band at the minimum (ambient q, Richardson FD) = [{'; '.join(' '.join(f'{x:+.5f}' for x in row) for row in R)}]  eigs={np.round(np.linalg.eigvalsh(R),5).tolist()}  Richardson change={np.max(np.abs(R-R0)):.1e}")
    log(f"[level {k} done in {time.time()-t0:.0f}s]")
    return E

if __name__ == "__main__":
    kmax = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    out = {}
    for k, grid, budget in [(1, 8, 60), (2, 6, 200), (3, 4, 400), (4, 0, 500)]:
        if k > kmax: break
        out[k] = run(k, grid, budget)
    log("\nSUMMARY periodic approximants (Bloch band bottom of 24 - A, cell = level-k FR30 supertile on 2^k Lambda_7):")
    for k, E in out.items(): log(f"  level {k}: E_per = {E:.6f}")
    log("  FR30 pinned finite patches (upper bounds on E_bulk): level 2: 10.77695, 3: 9.37847, 4: 8.91963, 5: 8.79701, 6: 8.77013")
    log(f"[total {time.time()-T0:.0f}s]")
