#!/usr/bin/env python3
"""Phase XI: independent audit and extension of the Z^3 laboratory (Phase X section 7).

Independent of audit/phase10_z3.py: links, plaquettes, Q8 classes (via quaternion coordinates), Bloch matrices, shadows and
certificates are re-implemented here; only the frame data of the Phase X pairs are read from the committed json.

Conventions (identical in meaning to Phase X; re-derived from PHASE10_REPORT section 7):
  sites q in Z^3, frames M_q (signed permutation matrices) periodic with period p; link U(q -> q + e_j) = (sigma.M_q^T e_j)(sigma.M_{q+e_j}^T e_j)
  H = 6 - A_U = D_U^+ D_U on l^2(Z^3) x C^2; Bloch matrix H(theta) on the unit cell, crossing links times e^{i theta_j}
  E_* = min_theta lambda_min H(theta)  (Bloch-Floquet); any H(theta) bounds E_* from above.
Subcommands:
  audit     rebuild the class-field-matched pair (phase10_z3_classpairs.json) and the trace-matched pair (phase10_z3_pairs.json):
            plaquette classes, shadow flatness of the ratio connection, both certified sides; float floors
  profile   the certified local frustration profile (Lambda_R, D_R) of A and B on Z^3 balls (Theorem XI.3 with D = 3)
  cover     cycle-cover (plaquette) curvature bounds (Theorem XI.5) for A, B and for fields with no trivial plaquette
  islands   frequency no-go at vanishing island density (Theorem XI.7)
Usage: python -u -I audit/phase11_z3.py <cmd> ... -> audit/results/phase11_z3.json (merged by key)"""
import os, sys, json, time, math, itertools, collections, types
from fractions import Fraction
sys.modules.setdefault('resource', types.SimpleNamespace(getrusage=lambda *a: types.SimpleNamespace(ru_maxrss=0), RUSAGE_SELF=0))
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); RES = os.path.join(HERE, 'results')
import numpy as np, scipy.sparse as sps
import phase11_chair as C11                      # only the generic certificate (banded_cert) and the IMS overlap c_overlap
T0 = time.time()
def log(*a): print(f"[{time.time()-T0:7.0f}s]", *a, flush=True)
OUT = os.path.join(RES, 'phase11_z3.json')
def save(key, obj):
    d = json.load(open(OUT)) if os.path.exists(OUT) else {}
    d[key] = obj; json.dump(d, open(OUT, 'w'), indent=1, default=float)

PAULI = np.array([[[0, 1], [1, 0]], [[0, -1j], [1j, 0]], [[1, 0], [0, -1]]], dtype=complex)
def sdot(v):
    k = int(np.argmax(np.abs(v))); assert abs(v).sum() == 1; return v[k] * PAULI[k]
def link(Ma, Mb, j):
    """(sigma . M_a^T e_j)(sigma . M_b^T e_j); M^T e_j = row j"""
    return sdot(Ma[j]) @ sdot(Mb[j])
def quat(W):
    """W = a 1 + b q1 + c q2 + d q3 with q_k = -i sigma_k: returns (a, b, c, d) (real), exact for Q8 elements"""
    a = np.trace(W).real / 2; b, c, d = [(np.trace(W @ PAULI[k]) / 2 * 1j).real for k in range(3)]
    return tuple(int(round(x)) for x in (a, b, c, d))
def q8_class(W):
    """'+1', '-1' or 'q1'/'q2'/'q3' (the axis of a traceless element; +-q_k are conjugate in Q8)"""
    a, b, c, d = quat(W); assert a * a + b * b + c * c + d * d == 1
    if a == 1: return '+1'
    if a == -1: return '-1'
    return 'q%d' % (1 + [b, c, d].index(next(x for x in (b, c, d) if x != 0)))
def angle(W):
    """minimal rotation angle theta in [0, pi]: W has eigenvalues e^{+-i theta}"""
    return math.acos(max(-1.0, min(1.0, np.trace(W).real / 2)))

class Field:
    def __init__(self, F):
        self.F = np.asarray(F, dtype=np.int64); self.p = self.F.shape[0]; self.n = self.p ** 3
    def site(self, q): p = self.p; return ((q[0] % p) * p + (q[1] % p)) * p + (q[2] % p)
    def M(self, q): return self.F[tuple(int(x) % self.p for x in q)]
    def U(self, q, j):
        q2 = np.array(q); q2[j] += 1; return link(self.M(q), self.M(q2), j)
    def bloch(self, theta):
        n = self.n; H = 6 * np.eye(2 * n, dtype=complex)
        for q in itertools.product(range(self.p), repeat=3):
            for j in range(3):
                q2 = list(q); q2[j] += 1; wrap = q2[j] // self.p; ph = np.exp(1j * theta[j] * wrap)
                a, b = self.site(q), self.site(q2); U = self.U(q, j)
                H[2 * a:2 * a + 2, 2 * b:2 * b + 2] -= ph * U; H[2 * b:2 * b + 2, 2 * a:2 * a + 2] -= np.conj(ph) * U.conj().T
        return H
    def lam(self, theta): return float(np.linalg.eigvalsh(self.bloch(np.asarray(theta, float)))[0])
    def floor(self, grid=6):
        from scipy.optimize import minimize
        ts = [2 * math.pi * k / grid for k in range(grid)]; vals = sorted((self.lam(t), t) for t in itertools.product(ts, repeat=3))
        best = vals[0][0]
        for v, t in vals[:3]:
            r = minimize(self.lam, np.array(t), method='Nelder-Mead', options={'xatol': 1e-8, 'fatol': 1e-12, 'maxiter': 3000})
            best = min(best, float(r.fun))
        return best
    def plaquettes(self):
        """{(q, i, j): W} for the plaquettes q -> q+e_i -> q+e_i+e_j -> q+e_j -> q of the unit cell"""
        out = {}
        for q in itertools.product(range(self.p), repeat=3):
            for i, j in ((0, 1), (0, 2), (1, 2)):
                q0 = np.array(q); ei = np.eye(3, dtype=int)[i]; ej = np.eye(3, dtype=int)[j]
                W = self.U(q0, i) @ self.U(q0 + ei, j) @ self.U(q0 + ej, i).conj().T @ self.U(q0, j).conj().T
                out[(q, i, j)] = W
        return out
    def free_cell(self):
        """the Neumann operator Deg - A on one unit cell (links inside the cell only)"""
        n = self.n; H = np.zeros((2 * n, 2 * n), complex); deg = np.zeros(n)
        for q in itertools.product(range(self.p), repeat=3):
            for j in range(3):
                q2 = list(q); q2[j] += 1
                if q2[j] >= self.p: continue
                a, b = self.site(q), self.site(q2); U = self.U(q, j)
                H[2 * a:2 * a + 2, 2 * b:2 * b + 2] -= U; H[2 * b:2 * b + 2, 2 * a:2 * a + 2] -= U.conj().T; deg[a] += 1; deg[b] += 1
        return H + np.diag(np.repeat(deg, 2))

def chi(k, W):
    """Abelian character of Q8 with kernel <q_k>: +1 on {+-1, +-q_k}, -1 on the other traceless elements"""
    c = q8_class(W); return 1 if c in ('+1', '-1', 'q%d' % k) else -1

def exact_rayleigh(H):
    """exact rational Rayleigh quotient of the rounded lowest eigenvector of a Hermitian matrix with Gaussian-integer entries"""
    w, V = np.linalg.eigh(H); v = V[:, 0] / np.abs(V[:, 0]).max(); s = 2 ** 24
    xr = [int(x) for x in np.rint(v.real * s)]; xi = [int(x) for x in np.rint(v.imag * s)]
    Hr = np.rint(H.real).astype(np.int64); Hi = np.rint(H.imag).astype(np.int64)
    assert np.array_equal(Hr, H.real) and np.array_equal(Hi, H.imag)
    n = len(xr); num = 0; den = sum(a * a + b * b for a, b in zip(xr, xi))
    for r in range(n):
        yr = sum(int(Hr[r, c]) * xr[c] - int(Hi[r, c]) * xi[c] for c in range(n) if Hr[r, c] or Hi[r, c])
        yi = sum(int(Hr[r, c]) * xi[c] + int(Hi[r, c]) * xr[c] for c in range(n) if Hr[r, c] or Hi[r, c])
        num += xr[r] * yr + xi[r] * yi
    return Fraction(num, den)

def certified_lower_dense(H, slack=1e-7):
    f = float(np.linalg.eigvalsh(H)[0]); mu = Fraction(math.floor((f - slack) * 2 ** 20), 2 ** 20)
    low, _ = C11.banded_cert(sps.csr_matrix(H), mu); return low

def load_pairs():
    d1 = json.load(open(os.path.join(RES, 'phase10_z3_classpairs.json')))['best']; d2 = json.load(open(os.path.join(RES, 'phase10_z3_pairs.json')))
    d2 = d2.get('best', d2)
    sh = lambda L: np.array(L).reshape(2, 2, 2, 3, 3)
    return {'class_matched': (Field(sh(d1['frames_low'])), Field(sh(d1['frames_high']))),
            'trace_matched': (Field(sh(d2['frames_low'])), Field(sh(d2['frames_high'])))}

def cmd_audit():
    out = {}
    for name, (A, B) in load_pairs().items():
        pa, pb = A.plaquettes(), B.plaquettes()
        ca = {k: q8_class(W) for k, W in pa.items()}; cb = {k: q8_class(W) for k, W in pb.items()}
        tr = lambda c: c if c in ('+1', '-1') else 'traceless'
        row = {'plaquettes_per_cell': len(pa), 'class_fields_identical': ca == cb,
               'trace_fields_identical': all(tr(ca[k]) == tr(cb[k]) for k in ca),
               'class_counts_A': dict(collections.Counter(ca.values())), 'class_counts_B': dict(collections.Counter(cb.values())),
               'plaquettes_with_different_class': sum(ca[k] != cb[k] for k in ca)}
        # shadows: the ratio connection nu = (chi_k o U_A)(chi_k o U_B) is flat on Z^3 iff every plaquette product is +1
        # (plaquettes generate the cycle space of Z^3); then the shadows are gauge-equivalent and unitarily equivalent on l^2(Z^3)
        flat = {}
        for k in (1, 2, 3):
            ok = True
            for key in pa:
                q, i, j = key; q0 = np.array(q); ei = np.eye(3, dtype=int)[i]; ej = np.eye(3, dtype=int)[j]
                prod = 1
                for (s, e) in ((q0, i), (q0 + ei, j), (q0 + ej, i), (q0, j)):
                    prod *= chi(k, A.U(s, e)) * chi(k, B.U(s, e))
                ok &= prod == 1
            flat[k] = bool(ok)
        row['shadow_ratio_flat'] = flat
        # certified sides
        qA = exact_rayleigh(A.bloch(np.zeros(3))); lowB = certified_lower_dense(B.free_cell())
        row.update({'E_A_upper_exact': f'{qA.numerator}/{qA.denominator}', 'E_A_upper': float(qA), 'E_B_lower_free_cell': lowB,
                    'certified_separation': lowB - float(qA), 'float_floor_A': A.floor(), 'float_floor_B': B.floor()})
        # shadow floors (float), for the record
        row['shadow_floors_A'] = [Field_shadow(A, k).floor() for k in (1, 2, 3)]; row['shadow_floors_B'] = [Field_shadow(B, k).floor() for k in (1, 2, 3)]
        # adjoint representation: Ad(Q8) = V4 is Abelian, so equal plaquette classes force equal plaquette ELEMENTS in SO(3);
        # the adjoint connections are then gauge-equivalent on Z^3 (plaquettes generate the cycle space): equal floors
        row['adjoint_plaquette_elements_identical'] = all(np.allclose(adjoint(pa[k]), adjoint(pb[k])) for k in pa)
        row['adjoint_floors_float'] = [AdjointField(A).floor(), AdjointField(B).floor()]
        out[name] = row; log(name, row)
    save('audit', out)

def adjoint(W):
    """SO(3) matrix of the adjoint action X -> W X W^+ on (sigma_1, sigma_2, sigma_3)"""
    return np.array([[0.5 * np.trace(PAULI[a] @ W @ PAULI[b] @ W.conj().T).real for b in range(3)] for a in range(3)])

class Field_shadow(Field):
    """chi_k o U (times the 2x2 identity): same Bloch structure"""
    def __init__(self, base, k): self.base, self.k = base, k; self.F, self.p, self.n = base.F, base.p, base.n
    def U(self, q, j): return chi(self.k, self.base.U(q, j)) * np.eye(2, dtype=complex)

class AdjointField(Field):
    """the adjoint (SO(3), 3-dimensional) representation of the same Q8 connection"""
    def __init__(self, base): self.base = base; self.F, self.p, self.n = base.F, base.p, base.n
    def U(self, q, j): return adjoint(self.base.U(q, j)).astype(complex)
    def bloch(self, theta):
        n = self.n; H = 6 * np.eye(3 * n, dtype=complex)
        for q in itertools.product(range(self.p), repeat=3):
            for j in range(3):
                q2 = list(q); q2[j] += 1; wrap = q2[j] // self.p; ph = np.exp(1j * theta[j] * wrap)
                a, b = self.site(q), self.site(q2); U = self.U(q, j)
                H[3 * a:3 * a + 3, 3 * b:3 * b + 3] -= ph * U; H[3 * b:3 * b + 3, 3 * a:3 * a + 3] -= np.conj(ph) * U.conj().T
        return H

# ------------------------------------------------------------------ the local frustration profile on Z^3 (Theorem XI.3, D = 3)
def ball_ops(field, centre, R, rho):
    """plain and amplified pinned operators on {q : |q - centre| < R} (Euclidean), amplification 1/c(1/rho) on every edge"""
    r = int(math.ceil(R)); pts = [np.array(centre) + np.array(o) for o in itertools.product(range(-r, r + 1), repeat=3) if sum(x * x for x in o) < R * R]
    idx = {tuple(q): i for i, q in enumerate(pts)}; n = len(pts); rows, cols, vals = [], [], []
    for q in pts:
        for j in range(3):
            q2 = q.copy(); q2[j] += 1
            if tuple(q2) not in idx: continue
            a, b = idx[tuple(q)], idx[tuple(q2)]; U = field.U(q, j); d = U.shape[0]
            for s in range(d):
                for t in range(d):
                    if U[s, t] != 0:
                        rows += [d * a + s, d * b + t]; cols += [d * b + t, d * a + s]; vals += [-U[s, t], -np.conj(U[s, t])]
    d = 2
    A = sps.csr_matrix((vals, (rows, cols)), shape=(d * n, d * n))
    amp = float(1 / C11.c_overlap(Fraction(1) / Fraction(rho)))
    return (6 * sps.identity(d * n) + A).tocsr(), (6 * sps.identity(d * n) + amp * A).tocsr(), amp, n

def cmd_profile(Rs=(3, 4, 5, 6, 7)):
    """(Lambda_R, D_R) for the class-matched pair: every Euclidean rho-ball lies in a ball of radius R = rho + sqrt(3)/2 about a
    lattice point; with period 2 the distinct lattice-point balls are the 8 translates of the unit cell"""
    out = {}
    A, B = load_pairs()['class_matched']
    for R in Rs:
        rho = Fraction(R) - Fraction(866026, 1000000)              # >= sqrt(3)/2 margin
        row = {}
        for nm, F in (('A', A), ('B', B)):
            Dmin, Lmin, Lcert = math.inf, math.inf, math.inf
            for c in itertools.product(range(2), repeat=3):
                Hp, Ha, amp, n = ball_ops(F, c, R, rho)
                lp = float(np.linalg.eigvalsh(Hp.toarray())[0]); la = float(np.linalg.eigvalsh(Ha.toarray())[0])
                mu = Fraction(math.floor((la - 1e-7) * 2 ** 20), 2 ** 20)
                low, _ = C11.banded_cert(Ha, mu, 6 * amp * 2.0 ** -52)
                Dmin, Lmin = min(Dmin, lp), min(Lmin, la); Lcert = min(Lcert, low if low is not None else -math.inf)
            row[nm] = {'D_R_float': Dmin, 'Lambda_R_float': Lmin, 'Lambda_R_certified': Lcert, 'ball_sites': n}
        row['separated'] = row['B']['Lambda_R_certified'] > row['A']['D_R_float']
        out[R] = row; log('profile R', R, row)
    save('profile', out)

# ------------------------------------------------------------------ cycle-cover bound (Theorem XI.5) on Z^3
def cover_bound(field):
    """E_* >= min_v sum_{plaquettes P ni v} lambda_P / max_e #{plaquettes P ni e} with lambda_P = 2(1 - cos(theta_P / 4)); on Z^3
    every vertex lies in 12 plaquettes and every edge in 4"""
    pl = field.plaquettes(); lam = {k: 2 * (1 - math.cos(angle(W) / 4)) for k, W in pl.items()}
    per_vertex = collections.defaultdict(float)
    for (q, i, j), l in lam.items():
        q0 = np.array(q); ei = np.eye(3, dtype=int)[i]; ej = np.eye(3, dtype=int)[j]
        for v in (q0, q0 + ei, q0 + ei + ej, q0 + ej): per_vertex[field.site(v)] += l
    return min(per_vertex.values()) / 4, dict(collections.Counter(q8_class(W) for W in pl.values()))

def cmd_cover(N=20000, seed=3):
    out = {}
    A, B = load_pairs()['class_matched']
    for nm, F in (('A', A), ('B', B)):
        b, cnt = cover_bound(F); out[nm] = {'cover_bound': b, 'class_counts': cnt}
    # period-2 Pauli-frame fields with NO trivial plaquette: the support statistic "no plaquette equals +1" forces
    # E_* >= 3 * 2(1 - cos(pi/8)) = 0.4567 (traceless angle pi/2); measure how close the true floors come
    SPM = [np.diag(s) @ np.eye(3, dtype=np.int64)[list(p)] for p in itertools.permutations(range(3)) for s in itertools.product((1, -1), repeat=3)]
    PROPER = [M for M in SPM if round(np.linalg.det(M)) == 1]
    rng = np.random.default_rng(seed); found = []
    for _ in range(N):
        F = Field(np.array([PROPER[i] for i in rng.integers(0, 24, 8)]).reshape(2, 2, 2, 3, 3))
        b, cnt = cover_bound(F)
        if cnt.get('+1', 0) == 0: found.append((F, b, cnt))
    rows = []
    for F, b, cnt in found[:60]:
        e = F.floor(grid=4); rows.append({'cover_bound': b, 'float_floor': e, 'class_counts': cnt})
    out['no_trivial_plaquette_fields'] = {'sampled': N, 'found': len(found), 'evaluated': rows,
                                          'min_floor': min((r['float_floor'] for r in rows), default=None),
                                          'universal_bound': 3 * 2 * (1 - math.cos(math.pi / 8))}
    log(out['no_trivial_plaquette_fields']['found'], out['no_trivial_plaquette_fields']['min_floor'])
    save('cover', out)

# ------------------------------------------------------------------ frequency no-go at vanishing density (Theorem XI.7)
def cmd_islands(seed=5):
    """start from the class-matched connection B (period 2, E_* >= 0.5858).  Period-M fields equal to B except on a flat island
    (constant frames) of side s: the frequency of every radius-1 environment changes by O(s^3 / M^3) + O(s^2 / M^3) -> 0 while
    E_* <= the island's Dirichlet value 6(1 - cos(pi/(s+1))) -> 0 (exact Rayleigh quotient of the product-sine bump)"""
    _, B = load_pairs()['class_matched']; rows = []
    for s, M in ((2, 6), (3, 10), (4, 16), (6, 30)):
        F = np.array([[[B.M((x, y, z)) for z in range(M)] for y in range(M)] for x in range(M)])
        for q in itertools.product(range(s), repeat=3): F[q] = np.eye(3, dtype=np.int64)
        Fi = Field(F); base = Field(np.array([[[B.M((x, y, z)) for z in range(M)] for y in range(M)] for x in range(M)]))
        # radius-1 environment of a site: the 6 links at the site as Q8 quaternions in a site gauge are not gauge invariant;
        # use the gauge-invariant multiset of plaquette classes at the site (12 plaquettes) as the environment statistic
        def env_hist(Fd):
            pl = Fd.plaquettes(); per = collections.defaultdict(list)
            for (q, i, j), W in pl.items():
                q0 = np.array(q); ei = np.eye(3, dtype=int)[i]; ej = np.eye(3, dtype=int)[j]
                for v in (q0, q0 + ei, q0 + ei + ej, q0 + ej): per[Fd.site(v)].append(q8_class(W))
            return collections.Counter(tuple(sorted(v)) for v in per.values())
        h1, h0 = env_hist(Fi), env_hist(base); tot = M ** 3
        tv = 0.5 * sum(abs(h1[k] - h0[k]) for k in set(h1) | set(h0)) / tot
        # trial vector: product-sine bump on the island (flat, trivial links), spinor e_1
        v = np.zeros(2 * tot)
        for q in itertools.product(range(s), repeat=3): v[2 * Fi.site(q)] = np.prod([math.sin(math.pi * (x + 1) / (s + 1)) for x in q])
        # Rayleigh quotient of 6 - A on l^2(Z^3) for a vector supported on the island: links inside the island are identity
        num = 0.0
        for q in itertools.product(range(s), repeat=3):
            a = v[2 * Fi.site(q)]; num += 6 * a * a
            for j in range(3):
                q2 = list(q); q2[j] += 1
                if q2[j] < s: num -= 2 * a * v[2 * Fi.site(q2)]
        rq = num / float(v @ v)
        rows.append({'island_side': s, 'period': M, 'island_density': s ** 3 / M ** 3, 'environment_TV_distance': tv,
                     'E_upper_island_bump': rq, 'closed_form': 6 * (1 - math.cos(math.pi / (s + 1)))})
        log(rows[-1])
    save('islands', rows)

if __name__ == '__main__':
    for c in sys.argv[1:]: globals()[f'cmd_{c}']()
