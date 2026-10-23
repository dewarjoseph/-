#!/usr/bin/env python3
"""Phase VII-B (E): matched controls for the Abelian-versus-Q8 comparison.  Everything lives on ONE graph (the level-L chair
supertile of the common substitution geometry: tile positions/shapes do not depend on the decoration), ONE operator
(pinned 24 - A_U, which is the compression of the infinite-volume operator to the supertile), and ONE flux statistic (holonomy
classes of the lattice-edge plaquettes with >= 2 owners, the Phase V-B/V-D definition: f_m1 = fraction with W = -1, f_trl =
fraction traceless).  Only the link variables differ:

  trivial       U = 1
  Z2_reflect    Clifford links of reflection-only frames (pi = id): +-1, Abelian; hull-covariant
  FR30          Clifford links of FR30 frames: Q8, non-Abelian; hull-covariant
  FR30_chi_k    the three Abelian shadows chi_k o U_FR30, chi_k: Q8 -> {+-1} the characters with kernel <q_k> (k = 1, 2, 3);
                same geometry, same hierarchy, same flux pattern modulo commutators; hull-covariant, Abelian
  rand_Q8_s     i.i.d. uniform Q8 link per panel (seed s)      rand_Z2_s   i.i.d. uniform +-1 per panel (seed s)

For each system and level: lambda_min (Lanczos) and, for L = 5, an exact Rayleigh-quotient upper certificate (a rational
number >= lambda_min of the same finite Hermitian matrix; for hull-covariant systems the level-5 supertile is a patch of every
hull element, so it also bounds the infinite-volume floor from above).  FR30's f_m1, f_trl are cross-checked against
phase5b_sweep.predictors.  Usage: python -u -I audit/phase7b_controls.py -> audit/results/phase7b_controls.json"""
import os, sys, json, time, itertools
from fractions import Fraction
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); RES = os.path.join(HERE, 'results')
import numpy as np, scipy.sparse as sps, scipy.sparse.linalg as sla
import phase7_local as P
import phase7_adversarial as A                      # Q8 table (MUL, INVQ, MAT, link_q)
from phase7_abelian_check import rayleigh_upper, REFLECTION_ONLY
from independent_clifford_q8_audit import FR30
T0 = time.time()
def log(*a): print(f"[{time.time()-T0:6.0f}s]", *a, flush=True)
SIGNED = [np.diag(s) @ np.eye(3, dtype=int)[list(p)] for p in itertools.permutations(range(3)) for s in itertools.product((1, -1), repeat=3)]
SKEY = {tuple(M.ravel()): i for i, M in enumerate(SIGNED)}
LQ = np.array([[[A.link_q(SIGNED[a], SIGNED[b], k) for k in range(3)] for b in range(48)] for a in range(48)], np.int8)   # link a -> b across normal e_k
CHI = {k: np.array([1 if (e // 2) in (0, k) else -1 for e in range(8)]) for k in (1, 2, 3)}       # chi_k(q) = +1 iff q in <q_k>

def geometry(dec, level):
    ops = P.make_ops(dec); P.GOPS = np.array([g for g, t in ops]); P.TOPS = np.array([t for g, t in ops])
    G, T = P.gen_poses(level); grid = P.owner_grid(level, G, T); fid = np.array([SKEY[tuple(np.asarray(g, int).ravel())] for g in G])
    return G, T, grid, fid

def panels(grid):
    """all panels (a, b, axis) with a the owner of the lower cube, as arrays, plus a dict for plaquette lookup"""
    N = grid.shape[0]; out = []
    for ax in range(3):
        sa = [slice(None)] * 3; sb = [slice(None)] * 3; sa[ax] = slice(0, N - 1); sb[ax] = slice(1, N)
        a, b = grid[tuple(sa)], grid[tuple(sb)]; m = (a >= 0) & (b >= 0) & (a != b)
        idx = np.argwhere(m); out.append((a[m], b[m], np.full(m.sum(), ax), idx))
    return out

def link_field(fid, pan, kind, rng=None):
    """Q8 index per panel (orientation lower -> upper owner); kind: clifford | trivial | randQ8 | randZ2"""
    res = []
    for a, b, ax, _ in pan:
        if kind == 'clifford': L = LQ[fid[a], fid[b], ax]
        elif kind == 'trivial': L = np.zeros(len(a), np.int8)
        elif kind == 'randQ8': L = rng.integers(0, 8, len(a)).astype(np.int8)
        elif kind == 'randZ2': L = rng.integers(0, 2, len(a)).astype(np.int8)          # indices 0 (+1), 1 (-1)
        res.append(L)
    return res

def operator(n, pan, links, chi=None):
    rows, cols, re, im = [], [], [], []
    for (a, b, ax, _), L in zip(pan, links):
        M = np.array(A.MAT)[L]
        if chi is not None: M = CHI[chi][L][:, None, None] * np.eye(2)[None]
        for i in range(2):
            for j in range(2):
                v = M[:, i, j]; nz = np.abs(v) > 0.5
                rows += list(2 * a[nz] + i); cols += list(2 * b[nz] + j); re += list(-np.rint(v[nz].real).astype(int)); im += list(-np.rint(v[nz].imag).astype(int))
                rows += list(2 * b[nz] + j); cols += list(2 * a[nz] + i); re += list(-np.rint(v[nz].real).astype(int)); im += list(np.rint(v[nz].imag).astype(int))
    d = np.arange(2 * n); rows += list(d); cols += list(d); re += [24] * (2 * n); im += [0] * (2 * n)
    Re = sps.csr_matrix((re, (rows, cols)), shape=(2 * n, 2 * n), dtype=np.int64); Im = sps.csr_matrix((im, (rows, cols)), shape=(2 * n, 2 * n), dtype=np.int64)
    assert (Re != Re.T).nnz == 0 and (Im + Im.T).nnz == 0
    return Re, Im

def plaquette_flux(grid, pan, links, chi=None):
    """holonomy classes of lattice-edge plaquettes with >= 2 distinct owners (cyclic order as phase5a_flux_vs_edge)"""
    N = grid.shape[0]; look = {}
    for (a, b, ax, idx), L in zip(pan, links):
        axv = int(ax[0])
        for (x, y, z), l in zip(map(tuple, idx), L): look[(int(x), int(y), int(z), axv)] = int(l)
    def cross(c, d, ax):                                       # Q8 index of the crossing from cube c to cube d = c +- e_ax
        lo = c if d[ax] > c[ax] else d; l = look.get((int(lo[0]), int(lo[1]), int(lo[2]), ax))
        if l is None: return 0                                 # same owner
        return l if d[ax] > c[ax] else int(A.INVQ[l])
    cls = [0, 0, 0]
    for m in range(3):
        a_, b_ = [x for x in range(3) if x != m]
        rng_ = [range(0, N) if ax_ == m else range(1, N) for ax_ in range(3)]   # as phase5a_flux_vs_edge: cubes P - s_a e_a - s_b e_b inside the box
        for Pt in itertools.product(*rng_):
            ea = np.zeros(3, int); ea[a_] = 1; eb = np.zeros(3, int); eb[b_] = 1; p = np.array(Pt)
            corners = [p, p - ea, p - ea - eb, p - eb]
            own = [grid[tuple(c)] for c in corners]
            if min(own) < 0 or len(set(own)) < 2: continue
            h = 0
            for i, j in ((0, 1), (1, 2), (2, 3), (3, 0)):
                ax = a_ if i in (0, 2) else b_
                h = int(A.MUL[h, cross(tuple(corners[i]), tuple(corners[j]), ax)])
            if chi is not None: h = 0 if CHI[chi][h] == 1 else 1
            cls[0 if h == 0 else (1 if h == 1 else 2)] += 1
    tot = sum(cls); return {'plaquettes': tot, 'f_m1': cls[1] / tot, 'f_trl': cls[2] / tot, 'f_nontriv': (cls[1] + cls[2]) / tot}

def bottom(Re, Im, certify):
    if certify: lam, q = rayleigh_upper(Re, Im); return lam, f'{q.numerator}/{q.denominator}', float(q)
    H = (Re + 1j * Im).astype(complex); return float(sla.eigsh(H, k=1, which='SA', tol=1e-10, return_eigenvectors=False)[0]), None, None

if __name__ == '__main__':
    out = {}; levels = (3, 4, 5)
    for L in levels:
        geo = {'fr30': geometry(FR30, L), 'refl': geometry(REFLECTION_ONLY, L)}
        Gf, Tf, gridf, fidf = geo['fr30']; Gr, Tr, gridr, fidr = geo['refl']
        setF = {frozenset(map(tuple, c)) for c in P.cubes_of_poses(Gf, Tf)}; setR = {frozenset(map(tuple, c)) for c in P.cubes_of_poses(Gr, Tr)}
        assert setF == setR, 'geometry differs'                                 # same chairs; tile labels differ (octant assignment depends on pi)
        n = len(Gf); panF = panels(gridf); panR = panels(gridr)
        assert sum(len(x[0]) for x in panF) == sum(len(x[0]) for x in panR)
        systems = {'trivial': (gridf, panF, link_field(fidf, panF, 'trivial'), None, True), 'Z2_reflect': (gridr, panR, link_field(fidr, panR, 'clifford'), None, True),
                   'FR30': (gridf, panF, link_field(fidf, panF, 'clifford'), None, True)}
        for k in (1, 2, 3): systems[f'FR30_chi{k}'] = (gridf, panF, systems['FR30'][2], k, True)
        for s in (1, 2):
            systems[f'rand_Q8_{s}'] = (gridf, panF, link_field(fidf, panF, 'randQ8', np.random.default_rng(100 + s)), None, False)
            systems[f'rand_Z2_{s}'] = (gridf, panF, link_field(fidf, panF, 'randZ2', np.random.default_rng(200 + s)), None, False)
        for name, (grid, pan, links, chi, cov) in systems.items():
            Re, Im = operator(n, pan, links, chi); lam, qs, qf = bottom(Re, Im, certify=(L == 5 and cov))
            rec = {'tiles': n, 'lambda_min': lam, 'rayleigh_upper_exact': qs, 'rayleigh_upper': qf, 'hull_covariant': cov}
            if L <= 4: rec.update(plaquette_flux(grid, pan, links, chi))
            out.setdefault(name, {})[L] = rec
            log(f"L{L} {name}: lambda_min {lam:.6f}" + (f"  Rayleigh <= {qf:.10f}" if qf else '') + (f"  f_m1 {rec['f_m1']:.4f} f_trl {rec['f_trl']:.4f}" if 'f_m1' in rec else ''))
        json.dump(out, open(os.path.join(RES, 'phase7b_controls.json'), 'w'), indent=1)
    # cross-check FR30 flux fractions with the Phase V-B predictor code at level 4
    import phase5b_sweep as sw
    from independent_clifford_q8_audit import tiles_at_level
    pr = sw.predictors(tiles_at_level(FR30, 4), 4); out['crosscheck_fr30_L4'] = {'phase5b_f_m1': pr['f_m1'], 'phase5b_f_trl': pr['f_trl']}
    log(f"cross-check FR30 L4 (phase5b_sweep.predictors): f_m1 {pr['f_m1']:.4f} f_trl {pr['f_trl']:.4f}")
    json.dump(out, open(os.path.join(RES, 'phase7b_controls.json'), 'w'), indent=1)
