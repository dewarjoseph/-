#!/usr/bin/env python3
"""Phase X, Part VII: a controlled second geometry -- periodic Pauli-frame connections on Z^3.

Geometry: unit cubes q in Z^3 are the tiles; two cubes are adjacent across a shared face (6 neighbours, no two-cycles).
Connection: a frame field q -> M_q (signed permutation matrices; periodic with period p in each direction) and the SAME Pauli
formula as on Chair44, U(q -> q + e_j) = (sigma.M_q^T e_j)(sigma.M_{q+e_j}^T e_j) in Q8.  Operator: H = 6 - A_U = D_U^+ D_U on
l^2(Z^3) x C^2 (the degree-normalised analogue of 24 - A_U).  Only the geometry differs from Chair44.

Infinite-volume floor (exact up to the minimisation over Bloch momenta): E_* = min_theta lambda_min(H(theta)), H(theta) the
Bloch matrix on the unit cell (2 p^3 dimensions).  Rigorous bounds: an upper bound from any theta (exact Rayleigh quotient at
theta = 0, where all entries are Gaussian integers), and a lower bound by branch and bound on the Brillouin torus using
|lambda_min(theta) - lambda_min(theta')| <= sum_j ||dH/dtheta_j|| |theta_j - theta'_j|, ||dH/dtheta_j|| <= 2 (one crossing link of
norm 1 in each direction per row), plus a floating-point margin.
Also computed: plaquette conjugacy classes (all 4 cubes distinct), the plaquette trace field, the free (Neumann) and pinned
cell operators (bracketing), and the Abelian shadows chi_k o U (chi_k: Q8 -> {+1,-1}, kernel <q_k>).
Usage: python -u -I audit/phase10_z3.py <cmd> ...  (cmds: noflat, pairs, certpair, classpairs, certclasspair, sample)  -> audit/results/phase10_z3_*.json"""
import os, sys, json, time, math, itertools, collections, types
sys.modules.setdefault('resource', types.SimpleNamespace(getrusage=lambda *a: types.SimpleNamespace(ru_maxrss=0), RUSAGE_SELF=0))
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); RES = os.path.join(HERE, 'results')
import numpy as np
T0 = time.time()
def log(*a): print(f"[{time.time()-T0:7.0f}s]", *a, flush=True)
SIG = np.array([[[0, 1], [1, 0]], [[0, -1j], [1j, 0]], [[1, 0], [0, -1]]], dtype=complex)
SPM = [np.diag(s) @ np.eye(3, dtype=int)[list(p)] for p in itertools.permutations(range(3)) for s in itertools.product((1, -1), repeat=3)]
PROPER = [M for M in SPM if round(np.linalg.det(M)) == 1]

def link(Ma, Mb, j):
    ra, rb = Ma[j], Mb[j]; ka, kb = int(np.abs(ra).argmax()), int(np.abs(rb).argmax())
    return ra[ka] * rb[kb] * (SIG[ka] @ SIG[kb])

class Cell:
    """periodic frame field with period p: frames[x, y, z] (signed permutation matrices)"""
    def __init__(self, frames):
        self.F = frames; self.p = frames.shape[0]; p = self.p; self.n = p ** 3
        self.idx = lambda q: ((q[0] % p) * p + (q[1] % p)) * p + (q[2] % p)
        self.links = {}                                                    # (site, j) -> (target site, crossing wrap vector, U)
        for q in itertools.product(range(p), repeat=3):
            for j in range(3):
                q2 = list(q); q2[j] += 1; wrap = np.zeros(3, int); wrap[j] = q2[j] // p
                self.links[(self.idx(q), j)] = (self.idx(q2), wrap, link(self.F[q], self.F[tuple(x % p for x in q2)], j))
    def bloch(self, theta):
        H = 6 * np.eye(2 * self.n, dtype=complex)
        for (a, j), (b, wrap, U) in self.links.items():
            ph = np.exp(1j * float(np.dot(wrap, theta))); H[2 * a:2 * a + 2, 2 * b:2 * b + 2] -= ph * U; H[2 * b:2 * b + 2, 2 * a:2 * a + 2] -= np.conj(ph) * U.conj().T
        return H
    def lam(self, theta): return float(np.linalg.eigvalsh(self.bloch(theta))[0])
    def floor(self, grid=8, refine=True):
        """numerical E_* = min over theta (grid then local Nelder-Mead from the best grid points)"""
        ts = [2 * math.pi * k / grid for k in range(grid)]; vals = sorted((self.lam(np.array(t)), t) for t in itertools.product(ts, repeat=3))
        best, arg = vals[0][0], np.array(vals[0][1])
        if refine:
            from scipy.optimize import minimize
            for v, t in vals[:4]:
                r = minimize(lambda th: self.lam(th), np.array(t), method='Nelder-Mead', options={'xatol': 1e-7, 'fatol': 1e-11, 'maxiter': 2000})
                if r.fun < best: best, arg = float(r.fun), r.x
        return best, arg
    def certified_lower(self, upper, tol=2e-3, max_boxes=200000):
        """branch and bound on the torus [0, 2pi)^3: returns a rigorous lower bound on min_theta lambda_min (within tol of upper)"""
        L = 2.0; margin = 1e-10 * 12; h0 = math.pi / 4; boxes = [(np.array(c) * 2 * h0 + h0, h0) for c in itertools.product(range(4), repeat=3)]
        lower, n_eval = float('inf'), 0
        while boxes:
            c, h = boxes.pop(); v = self.lam(c); n_eval += 1; lb = v - L * 3 * h - margin
            if lb >= upper - tol: lower = min(lower, lb); continue
            if n_eval > max_boxes: return None, n_eval
            for d in itertools.product((-0.5, 0.5), repeat=3): boxes.append((c + np.array(d) * h, h / 2))
            if h < 1e-6: lower = min(lower, lb); continue
        return min(lower, upper - tol), n_eval
    def plaquettes(self):
        """holonomy class of every plaquette of the unit cell (cube corner q, plane (i, j), i < j): 10 (+1), 11 (-1), 0/1/2 (axis)"""
        out = {}
        for q in itertools.product(range(self.p), repeat=3):
            for i, j in ((0, 1), (0, 2), (1, 2)):
                ei, ej = np.eye(3, dtype=int)[i], np.eye(3, dtype=int)[j]; qs = [np.array(q), np.array(q) + ei, np.array(q) + ei + ej, np.array(q) + ej]
                W = np.eye(2, dtype=complex)
                for a, b in zip(qs, qs[1:] + qs[:1]):
                    d = b - a; ax = int(np.abs(d).argmax()); Fa, Fb = self.F[tuple(a % self.p)], self.F[tuple(b % self.p)]
                    W = W @ link(Fa, Fb, ax)
                tr = np.real(np.trace(W)); c = 10 if np.isclose(tr, 2) else 11 if np.isclose(tr, -2) else int(np.argmax([abs(np.trace(W @ S)) for S in SIG]))
                out[(q, i, j)] = c
        return out
    def cell_ops(self):
        """pinned (6 - A) and free (Deg - A) operators on one unit cell with open boundaries"""
        n = self.n; Hp = 6 * np.eye(2 * n, dtype=complex); deg = np.zeros(n)
        for (a, j), (b, wrap, U) in self.links.items():
            if wrap.any(): continue
            Hp[2 * a:2 * a + 2, 2 * b:2 * b + 2] -= U; Hp[2 * b:2 * b + 2, 2 * a:2 * a + 2] -= U.conj().T; deg[a] += 1; deg[b] += 1
        return Hp, Hp - np.diag(np.repeat(6 - deg, 2))

def random_cell(rng, p=2, frames=PROPER): return np.array([frames[i] for i in rng.integers(0, len(frames), p ** 3)]).reshape(p, p, p, 3, 3)
def counts(pl): c = collections.Counter(pl.values()); return (c[10], c[11], c[0] + c[1] + c[2])
def trace_field(pl): return tuple(sorted((k, (v if v >= 10 else 3)) for k, v in pl.items()))
def q8_class(U):
    tr = np.real(np.trace(U))
    return 10 if np.isclose(tr, 2) else 11 if np.isclose(tr, -2) else int(np.argmax([abs(np.trace(U @ S)) for S in SIG]))

class Shadow(Cell):
    """the Abelian shadow chi_k o U: every link replaced by chi_k(U) in {+1, -1} (times the 2x2 identity)"""
    def __init__(self, cell, k):
        self.F, self.p, self.n, self.idx = cell.F, cell.p, cell.n, cell.idx; self.links = {}
        for key, (b, wrap, U) in cell.links.items():
            c = q8_class(U); chi = 1 if c in (10, 11, k) else -1; self.links[key] = (b, wrap, chi * np.eye(2, dtype=complex))

def gauge_key(cell):
    """tree-gauge holonomies of the periodic connection on the 3-torus of side p (spanning tree from site 0): gauge-equivalent
    connections have keys related by one global conjugation; the wrap phases are recorded so that Bloch-equivalent ones agree"""
    adj = collections.defaultdict(list)
    for (a, j), (b, wrap, U) in cell.links.items(): adj[a].append((b, U, wrap)); adj[b].append((a, U.conj().T, -wrap))
    g = {0: np.eye(2, dtype=complex)}; q = collections.deque([0]); used = set()
    while q:
        a = q.popleft()
        for b, U, w in adj[a]:
            if b not in g: g[b] = g[a] @ U; used.add((min(a, b), max(a, b), tuple(w), 'x')); q.append(b)
    return g

def certify_pair(c1, c2):
    """rigorous E_* bounds for two cells: exact Rayleigh at the numerical minimiser is replaced by the theta = 0 matrix bound
    when theta = 0 is the minimiser; lower bounds by branch and bound"""
    out = []
    for c in (c1, c2):
        E, th = c.floor(grid=8); up = E + 1e-9                               # float upper value at the minimiser (+ rounding margin)
        lo, nev = c.certified_lower(up, tol=2e-3); out.append({'E_float': E, 'theta': list(map(float, th)), 'lower': lo, 'upper': up, 'evaluations': nev})
    return out

def cmd_sample(N=2000, p=3, seed=20261024):
    """random period-3 frame fields: floors, class counts, trace fields, cell bounds and the three Abelian shadow floors"""
    rng = np.random.default_rng(seed); rows = []
    for it in range(N):
        F = random_cell(rng, p); c = Cell(F); E, th = c.floor(grid=5); pl = c.plaquettes(); Hp, Hf = c.cell_ops()
        sh = [Shadow(c, k).floor(grid=5)[0] for k in range(3)]
        rows.append({'frames': F.reshape(-1, 9).tolist(), 'E': E, 'theta': list(map(float, th)), 'counts': counts(pl), 'trace_key': str(hash(trace_field(pl))),
                     'pinned_cell': float(np.linalg.eigvalsh(Hp)[0]), 'free_cell': float(np.linalg.eigvalsh(Hf)[0]), 'shadow_E': sh})
        if it % 200 == 0: log(f"sample {it}: E {E:.4f} counts {rows[-1]['counts']} shadows {np.round(sh, 4).tolist()}")
    json.dump({'p': p, 'seed': seed, 'rows': rows}, open(os.path.join(RES, 'phase10_z3_sample.json'), 'w'))

def cmd_pairs(N=40000, p=2, seed=7):
    """period-2 search for two frame fields with IDENTICAL plaquette trace fields (hence identical class counts and Wilson
    action) and different floors; the best-separated pair is certified"""
    rng = np.random.default_rng(seed); by = collections.defaultdict(list)
    for it in range(N):
        F = random_cell(rng, p); c = Cell(F); pl = c.plaquettes(); key = trace_field(pl)
        if len(by[key]) < 6: by[key].append(F)
    found = []
    for key, Fs in by.items():
        if len(Fs) < 2: continue
        Es = [(Cell(F).floor(grid=6)[0], F) for F in Fs]; Es.sort(key=lambda x: x[0])
        if Es[-1][0] - Es[0][0] > 1e-3: found.append((Es[-1][0] - Es[0][0], Es[0], Es[-1], key))
    found.sort(key=lambda x: -x[0]); log(f"{len(by)} distinct trace fields, {sum(len(v) >= 2 for v in by.values())} shared, {len(found)} with different floors")
    out = {'p': p, 'N': N, 'seed': seed, 'distinct_trace_fields': len(by), 'shared': sum(len(v) >= 2 for v in by.values()), 'pairs_with_different_floor': len(found)}
    if found:
        gap, (E1, F1), (E2, F2), key = found[0]; c1, c2 = Cell(F1), Cell(F2)
        cert = certify_pair(c1, c2); pl1, pl2 = c1.plaquettes(), c2.plaquettes()
        out['best'] = {'gap_float': gap, 'frames_low': F1.reshape(-1, 9).tolist(), 'frames_high': F2.reshape(-1, 9).tolist(), 'certificate': cert,
                       'trace_fields_identical': trace_field(pl1) == trace_field(pl2), 'class_counts': [counts(pl1), counts(pl2)],
                       'certified_separation': (cert[1]['lower'] - cert[0]['upper']) if cert[1]['lower'] is not None else None}
        log('best pair', {k: v for k, v in out['best'].items() if not k.startswith('frames')})
    json.dump(out, open(os.path.join(RES, 'phase10_z3_pairs.json'), 'w'), default=float)

def exact_rayleigh_dense(H):
    """exact rational Rayleigh quotient of the rounded lowest eigenvector of a Gaussian-integer Hermitian matrix"""
    from fractions import Fraction
    w, V = np.linalg.eigh(H); v = V[:, 0] / np.abs(V[:, 0]).max(); s = 2 ** 20
    Re, Im = np.rint(H.real).astype(np.int64), np.rint(H.imag).astype(np.int64); assert np.allclose(Re + 1j * Im, H)
    xr, xi = np.rint(v.real * s).astype(np.int64), np.rint(v.imag * s).astype(np.int64); yr, yi = Re @ xr - Im @ xi, Re @ xi + Im @ xr
    num = sum(int(a) * int(b) for a, b in zip(xr, yr)) + sum(int(a) * int(b) for a, b in zip(xi, yi)); den = sum(int(a) ** 2 for a in xr) + sum(int(a) ** 2 for a in xi)
    return Fraction(num, den)

def cmd_certpair():
    """rigorous infinite-volume separation for the best trace-field-matched pair:
       E_*(low) <= exact Rayleigh quotient of H_low(theta = 0) (every Bloch matrix bounds the floor from above);
       E_*(high) >= lambda_min of the free 2x2x2 cell (Z^3 is partitioned into cells; dropping the inter-cell links is a
       lower bound: Dirichlet-Neumann bracketing), certified by the Higham Cholesky test"""
    import phase9_pair as P9
    from fractions import Fraction
    d = json.load(open(os.path.join(RES, 'phase10_z3_pairs.json'))); b = d['best']; out = dict(d)
    lo_cell, hi_cell = Cell(np.array(b['frames_low']).reshape(2, 2, 2, 3, 3)), Cell(np.array(b['frames_high']).reshape(2, 2, 2, 3, 3))
    q = exact_rayleigh_dense(lo_cell.bloch(np.zeros(3))); _, Hf = hi_cell.cell_ops(); f = float(np.linalg.eigvalsh(Hf)[0])
    mu = Fraction(math.floor((f - 1e-7) * 2 ** 20), 2 ** 20); low = P9.certified_lower(__import__('scipy.sparse', fromlist=['csr_matrix']).csr_matrix(Hf), mu)
    pl_lo, pl_hi = lo_cell.plaquettes(), hi_cell.plaquettes()
    out['certificate_v2'] = {'E_low_upper_exact': f'{q.numerator}/{q.denominator}', 'E_low_upper': float(q), 'E_high_lower_free_cell': low,
                             'certified_separation': low - float(q), 'trace_fields_identical': trace_field(pl_lo) == trace_field(pl_hi),
                             'full_class_fields_identical': pl_lo == pl_hi, 'class_fields_differ_at': sum(1 for k in pl_lo if pl_lo[k] != pl_hi[k]),
                             'shadow_floors_low': [Shadow(lo_cell, k).floor(grid=6)[0] for k in range(3)], 'shadow_floors_high': [Shadow(hi_cell, k).floor(grid=6)[0] for k in range(3)]}
    # falsification of "the non-Abelian floor is at least every Abelian-shadow floor": certified lower bounds (free cell) for the
    # shadows of the low connection against its exact upper bound
    sh = []
    for k in range(3):
        _, Hfs = Shadow(lo_cell, k).cell_ops(); fs = float(np.linalg.eigvalsh(Hfs)[0])
        if fs > 1e-6:
            mus = Fraction(math.floor((fs - 1e-7) * 2 ** 20), 2 ** 20); sh.append(P9.certified_lower(__import__('scipy.sparse', fromlist=['csr_matrix']).csr_matrix(Hfs), mus))
        else: sh.append(0.0)
    out['certificate_v2']['shadow_lower_bounds_low'] = sh
    out['certificate_v2']['shadow_exceeds_nonabelian_certified'] = [s > float(q) for s in sh]
    log(out['certificate_v2']); json.dump(out, open(os.path.join(RES, 'phase10_z3_pairs.json'), 'w'), default=float)

def cmd_classpairs(N=40000, p=2, seed=7):
    """the same random fields keyed by the FULL Q8 class field (with axes): equal classes plaquette by plaquette, different floors?"""
    rng = np.random.default_rng(seed); by = collections.defaultdict(list)
    for it in range(N):
        F = random_cell(rng, p); c = Cell(F); key = tuple(sorted(c.plaquettes().items()))
        if len(by[key]) < 6: by[key].append(F)
    found = []
    for key, Fs in by.items():
        if len(Fs) < 2: continue
        Es = sorted(((Cell(F).floor(grid=6)[0], i) for i, F in enumerate(Fs)))
        if Es[-1][0] - Es[0][0] > 1e-3: found.append((Es[-1][0] - Es[0][0], Fs[Es[0][1]], Fs[Es[-1][1]]))
    found.sort(key=lambda x: -x[0]); out = {'N': N, 'distinct_class_fields': len(by), 'shared': sum(len(v) >= 2 for v in by.values()), 'pairs_with_different_floor': len(found)}
    if found:
        gap, F1, F2 = found[0]; c1, c2 = Cell(F1), Cell(F2); q = exact_rayleigh_dense(c1.bloch(np.zeros(3))); _, Hf = c2.cell_ops()
        import phase9_pair as P9, scipy.sparse as sp
        from fractions import Fraction
        f = float(np.linalg.eigvalsh(Hf)[0]); mu = Fraction(math.floor((f - 1e-7) * 2 ** 20), 2 ** 20); low = P9.certified_lower(sp.csr_matrix(Hf), mu)
        out['best'] = {'gap_float': gap, 'frames_low': F1.reshape(-1, 9).tolist(), 'frames_high': F2.reshape(-1, 9).tolist(), 'E_low_upper': float(q),
                       'E_high_lower_free_cell': low, 'certified_separation': low - float(q)}
    log({k: v for k, v in out.items() if k != 'best'}, out.get('best', {}).get('certified_separation'))
    json.dump(out, open(os.path.join(RES, 'phase10_z3_classpairs.json'), 'w'), default=float)

def cmd_certclasspair():
    """the certificate for the best class-field-matched pair: identical Q8 conjugacy class on EVERY plaquette, hence identical
    trace fields and, since chi_k is a class function and the plaquettes generate the cycle space of Z^3, gauge-equivalent Abelian
    shadows chi_k o U (identical shadow floors); E_*(A) <= exact Rayleigh at theta = 0 < free-cell certified bound <= E_*(B)"""
    import phase9_pair as P9, scipy.sparse as sp
    from fractions import Fraction
    p = os.path.join(RES, 'phase10_z3_classpairs.json'); d = json.load(open(p)); b = d['best']
    A, B = (Cell(np.array(b[k]).reshape(2, 2, 2, 3, 3)) for k in ('frames_low', 'frames_high')); pa, pb = A.plaquettes(), B.plaquettes()
    q = exact_rayleigh_dense(A.bloch(np.zeros(3))); _, Hf = B.cell_ops(); f = float(np.linalg.eigvalsh(Hf)[0])
    low = P9.certified_lower(sp.csr_matrix(Hf), Fraction(math.floor((f - 1e-7) * 2 ** 20), 2 ** 20))
    d['certificate'] = {'class_fields_identical': pa == pb, 'trace_fields_identical': trace_field(pa) == trace_field(pb), 'class_counts': counts(pa),
                        'E_low_upper_exact': f'{q.numerator}/{q.denominator}', 'E_low_upper': float(q), 'E_high_lower_free_cell': low, 'certified_separation': low - float(q),
                        'float_floors': [A.floor(grid=6)[0], B.floor(grid=6)[0]],
                        'shadow_floors_low': [Shadow(A, k).floor(grid=6)[0] for k in range(3)], 'shadow_floors_high': [Shadow(B, k).floor(grid=6)[0] for k in range(3)]}
    log(d['certificate']); json.dump(d, open(p, 'w'), default=float)

def cmd_noflat(seed=11):
    """no-go construction: period-L fields with a flat island (constant frames on an R-cube) and random frames elsewhere.  The
    fraction of non-trivial plaquettes stays high while E_* <= Rayleigh quotient of a gauge-fixed bump on the island -> 0."""
    rng = np.random.default_rng(seed); rows = []
    for R in (2, 3, 4, 6, 8):
        L = 2 * R; F = random_cell(rng, L)
        for q in itertools.product(range(R), repeat=3): F[q] = PROPER[0]
        c = Cell(F); pl = c.plaquettes(); cnt = counts(pl); frac = (cnt[1] + cnt[2]) / sum(cnt)
        H = c.bloch(np.zeros(3)); n = c.n
        # trial vector: sin bump on the island, constant spinor (the island is flat with trivial links), zero elsewhere
        v = np.zeros(2 * n, complex)
        for q in itertools.product(range(R), repeat=3): v[2 * c.idx(q)] = np.prod([math.sin(math.pi * (x + 1) / (R + 1)) for x in q])
        rq = float(np.real(v.conj() @ H @ v) / np.real(v.conj() @ v))
        rows.append({'R': R, 'L': L, 'nontrivial_plaquette_fraction': frac, 'rayleigh_upper_on_E': rq, 'bound_6sin2': 6 * (1 - math.cos(math.pi / (R + 1)))})
        log(rows[-1])
    json.dump({'rows': rows}, open(os.path.join(RES, 'phase10_z3_noflat.json'), 'w'))

if __name__ == '__main__':
    for cmd in sys.argv[1:]: globals()[f'cmd_{cmd}']()
