#!/usr/bin/env python3
"""Phase XIII: an independent reconstruction, in exact arithmetic, of the counting algorithm of "The Exponential Time
Hypothesis is False" (openai/math, Family 378, 25 October 2026; preprints/.../build/main_full_version.tex).

Written from the paper's Sections 2-4 alone (no code from the openai/math repository is executed, and no other prototype is
used).  Numbering as in the paper: Definition 3.1 (layout), Lemma 3.2 (separation by measurements), Lemma 3.3 (Boolean
differences), Proposition 3.4 (counting routine), Lemma 4.1 (C^B), Lemma 4.2 (support of M_0), Lemma 4.3 (rows P_u),
Remark 4.4, Section 4.4 (placing copies), Lemma 4.6 (denominators).

Objects.
  B = ([r]^Q)^2, u = (a_u, d_u), D = r^(2Q); swap theta_s exchanges a_u(s), d_u(s); (Pi_s zeta)_u = zeta_{theta_s(u)};
  V_0 = prod Pi_s, W_0 = (1/2) sum (I - Pi_s), f_I(z) = (-1)^A0 sum_{j<R} (-2)^j binom(z - A0, j), M_0 = V_0 f_I(W_0);
  C^B = the product eigenvectors psi with j(psi) not in I = {A0, ..., A0+R-1};
  P_u(T) = delta_u (I - M_0) + sum_y M_0[u, y] phi_{u,y}(T) delta_y, phi_{u,y}(T) = prod_{s in E_{u,y}} (1 - T/s),
  E_{u,y} = {s : a_y(s) != d_u(s)}.
M_0 is formed from the expansion f_I(W_0) = sum_{S subset [Q]} g(|S|) Pi_S (the Pi_s are commuting involutions, so the
coefficient depends on |S| only and is the Krawtchouk transform of f_I on {0..Q}); a test compares it with the direct matrix
evaluation.  Arithmetic is over Fraction, or over GF(p), p = 2^61 - 1, through the same code (class Field): every identity is a
polynomial identity over Q whose denominators divide (R-1)! Q! and the Hermite determinant, so a GF(p) run is the image of the
rational run, and since 0 <= #F <= 2^n < p, H(0) = #F mod p is the exact count.
Usage: python -u -I audit/phase13_eth.py -> audit/results/phase13_eth.json (the verification battery)"""
import itertools, math, random, json, os, sys, time
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__)); RES = os.path.join(HERE, 'results')
PRIME = 2 ** 61 - 1

class Field:
    """Q (exact Fractions) or GF(PRIME)"""
    def __init__(self, modular):
        self.modular = modular
    def c(self, x):
        if not self.modular: return Fraction(x)
        x = Fraction(x); return x.numerator % PRIME * pow(x.denominator % PRIME, PRIME - 2, PRIME) % PRIME
    def add(self, a, b): return (a + b) % PRIME if self.modular else a + b
    def sub(self, a, b): return (a - b) % PRIME if self.modular else a - b
    def mul(self, a, b): return a * b % PRIME if self.modular else a * b
    def inv(self, a):
        if self.modular:
            assert a % PRIME, 'division by zero mod p'; return pow(a, PRIME - 2, PRIME)
        return 1 / a
    def zero(self): return 0 if self.modular else Fraction(0)
    def one(self): return 1 if self.modular else Fraction(1)

# ---------------------------------------------------------------- polynomials (lists of coefficients, low degree first)
def padd(F, p, q):
    n = max(len(p), len(q)); return [F.add(p[i] if i < len(p) else F.zero(), q[i] if i < len(q) else F.zero()) for i in range(n)]
def pscale(F, p, a): return [F.mul(a, x) for x in p]
def pmul(F, p, q, J=None):
    n = len(p) + len(q) - 1 if J is None else min(J, len(p) + len(q) - 1)
    out = [F.zero()] * max(n, 0)
    for i, a in enumerate(p):
        if i >= n: break
        if a == 0: continue
        for j, b in enumerate(q):
            if i + j >= n: break
            out[i + j] = F.add(out[i + j], F.mul(a, b))
    return out
def peval(F, p, t):
    acc = F.zero()
    for a in reversed(p): acc = F.add(F.mul(acc, t), a)
    return acc
def pshift(F, p, t, J):
    """coefficients of p(t + z) mod z^J"""
    out = [F.zero()] * J
    for k, a in enumerate(p):
        if a == 0: continue
        for j in range(min(k, J - 1) + 1):
            out[j] = F.add(out[j], F.mul(a, F.c(math.comb(k, j) * t ** (k - j))))
    return out

# ---------------------------------------------------------------- Section 4: the auxiliary rows
def krawtchouk(Q, k, j): return sum((-1) ** i * math.comb(j, i) * math.comb(Q - j, k - i) for i in range(0, min(j, k) + 1))

class Aux:
    def __init__(self, r, Q, R, A0=None):
        assert r >= 2 and Q >= 1 and R >= 1
        self.r, self.Q, self.R = r, Q, R
        if A0 is None: A0 = math.floor(Fraction(Q * (r - 1), 2 * r) - Fraction(R - 1, 2))   # Lemma 4.8's interval
        assert 0 <= A0 and A0 + R - 1 <= Q, 'interval outside {0..Q}'
        self.A0, self.I = A0, set(range(A0, A0 + R))
        self.seqs = list(itertools.product(range(r), repeat=Q)); self.K = len(self.seqs); self.D = self.K ** 2
        self.sidx = {s: i for i, s in enumerate(self.seqs)}
        self.labels = [(a, d) for a in self.seqs for d in self.seqs]              # u = ia * K + id
        self.index = {lab: i for i, lab in enumerate(self.labels)}
        # f_I on {0..Q}, and its expansion coefficients g(k) in the swaps
        self.fvals = [self.f(Fraction(j)) for j in range(Q + 1)]
        self.g = [sum(math.comb(Q, j) * self.fvals[j] * krawtchouk(Q, k, j) for j in range(Q + 1)) / (2 ** Q * math.comb(Q, k))
                  for k in range(Q + 1)]
        self._M0 = None

    def f(self, z):
        """f_I(z) = (-1)^A0 sum_{j<R} (-2)^j binom(z - A0, j)"""
        tot = Fraction(0)
        for j in range(self.R):
            b = Fraction(1)
            for a in range(j): b *= (z - self.A0 - a)
            tot += (-2) ** j * b / math.factorial(j)
        return (-1) ** self.A0 * tot

    def swap(self, u, T):
        """theta_T(u): exchange a_u(s), d_u(s) for s in T (positions 0-based)"""
        a, d = map(list, self.labels[u])
        for s in T: a[s], d[s] = d[s], a[s]
        return self.index[(tuple(a), tuple(d))]

    def M0(self):
        """sparse rows {u: {y: M0[u,y]}} from M_0 = V_0 f(W_0) = sum_S g(|S|) Pi_{[Q] minus S}"""
        if self._M0 is None:
            Q = self.Q; rows = []
            subsets = [T for k in range(Q + 1) for T in itertools.combinations(range(Q), k)]
            for u in range(self.D):
                row = {}
                for T in subsets:
                    coef = self.g[Q - len(T)]
                    if coef == 0: continue
                    y = self.swap(u, T); row[y] = row.get(y, 0) + coef
                rows.append({y: c for y, c in row.items() if c != 0})
            self._M0 = rows
        return self._M0

    def E(self, u, y):
        du = self.labels[u][1]; ay = self.labels[y][0]
        return [s for s in range(self.Q) if ay[s] != du[s]]

    def _make_basis(self):
        """the product eigenbasis of Lemma 4.1: list of (j, {u: +-1})"""
        r, Q = self.r, self.Q
        one = [(+1, {(a, a): 1}) for a in range(r)]
        one += [(+1, {(a, b): 1, (b, a): 1}) for a in range(r) for b in range(a + 1, r)]
        one += [(-1, {(a, b): 1, (b, a): -1}) for a in range(r) for b in range(a + 1, r)]
        out = []
        for choice in itertools.product(one, repeat=Q):
            j = sum(1 for sg, _ in choice if sg == -1); vec = {(): 1}
            for s, (_, fn) in enumerate(choice):
                vec = {k + (pair,): v * w for k, v in vec.items() for pair, w in fn.items()}
            psi = {}
            for k, v in vec.items():
                a = tuple(p[0] for p in k); d = tuple(p[1] for p in k); psi[self.index[(a, d)]] = v
            out.append((j, psi))
        return out

    def basis(self):
        if not hasattr(self, '_basis'): self._basis = self._make_basis()
        return self._basis

    def CB(self):
        if not hasattr(self, '_CB'): self._CB = [psi for j, psi in self.basis() if j not in self.I]
        return self._CB

    def row(self, u):
        if not hasattr(self, '_rows'): self._rows = {}
        if u not in self._rows: self._rows[u] = self._make_row(u)
        return self._rows[u]

    def _make_row(self, u):
        """P_u(T) as {y: [coefficients in T]} (exact Fractions)"""
        M = self.M0()[u]; out = {}
        def acc(y, poly):
            cur = out.get(y, [Fraction(0)])
            n = max(len(cur), len(poly)); out[y] = [(cur[i] if i < len(cur) else 0) + (poly[i] if i < len(poly) else 0) for i in range(n)]
        acc(u, [Fraction(1)])
        for y, m in M.items():
            acc(y, [-m])                                                    # delta_u (I - M_0)
            phi = [Fraction(1)]
            for s in self.E(u, y): phi = pmul(Field(False), phi, [Fraction(1), Fraction(-1, s + 1)])   # points are 1..Q
            acc(y, [m * c for c in phi])
        return {y: p for y, p in out.items() if any(c != 0 for c in p)}

# ---------------------------------------------------------------- formulas, labels, Section 4.4 transfer
def random_bounded_3cnf(n, m, rng, occ=3):
    """m clauses of width <= 3 on n variables, each variable in at most occ clauses (the overview's setting)"""
    left = {v: occ for v in range(n)}; clauses = []
    for _ in range(m):
        cand = [v for v in range(n) if left[v] > 0]
        if len(cand) < 1: break
        w = min(3, len(cand)); vs = rng.sample(cand, w)
        for v in vs: left[v] -= 1
        clauses.append([(v, rng.random() < 0.5) for v in vs])                # (variable, positive?)
    return clauses

def brute_count(n, clauses):
    return sum(all(any((x >> v & 1) == pos for v, pos in cl) for cl in clauses) for x in range(2 ** n))

class Layout:
    """Definition 3.1 data built by Section 4.4 from an Aux and arbitrary (seeded) schedules a_v, d_f"""
    def __init__(self, aux, n, clauses, seed=0):
        rng = random.Random(seed); self.aux, self.n = aux, n
        used = {v for cl in clauses for v, _ in cl}
        self.factors = [('clause', cl) for cl in clauses] + [('dummy', [(v, True)]) for v in range(n) if v not in used]
        self.scopes = [[v for v, _ in cl] for _, cl in self.factors]
        Q, r = aux.Q, aux.r
        self.a = [tuple(rng.randrange(r) for _ in range(Q)) for _ in range(n)]
        self.d = [tuple(rng.randrange(r) for _ in range(Q)) for _ in self.factors]
        # copies: distinct (copy, label) per incidence
        seen = {}; self.place = {}
        for f, sc in enumerate(self.scopes):
            for v in sc:
                u = aux.index[(self.a[v], self.d[f])]; c = seen.get(u, 0); seen[u] = c + 1; self.place[(f, v)] = (c, u)
        self.h = max(seen.values()); self.occupant = {pos: v for (f, v), pos in self.place.items()}
        self._rows = {}

    def P(self, f, v):
        """P_{f,v}(T) on the actual variables: {v': [coefficients in T]} (Fractions)"""
        if (f, v) not in self._rows:
            c, u = self.place[(f, v)]; out = {}
            for y, poly in self.aux.row(u).items():
                w = self.occupant.get((c, y))
                if w is None: continue                                        # unused position, fixed at zero
                cur = out.get(w, [Fraction(0)]); n = max(len(cur), len(poly))
                out[w] = [(cur[i] if i < len(cur) else 0) + (poly[i] if i < len(poly) else 0) for i in range(n)]
            self._rows[(f, v)] = {w: p for w, p in out.items() if any(c != 0 for c in p)}
        return self._rows[(f, v)]

    def group(self, t, g): return [v for v in range(self.n) if self.a[v][t - 1] == g]
    def sigma(self, f, t): return self.d[f][t - 1]

    def C(self, t, g, keep_zero=False):
        """C_{t,g}: rows (copy, psi) of diag(C^B, ..., C^B) iota restricted to the columns S_{t,g}"""
        if not hasattr(self, '_C'): self._C = {}
        if (t, g, keep_zero) not in self._C: self._C[(t, g, keep_zero)] = self._make_C(t, g, keep_zero)
        return self._C[(t, g, keep_zero)]

    def _make_C(self, t, g, keep_zero):
        S = self.group(t, g); col = {v: i for i, v in enumerate(S)}; out = []
        for c in range(self.h):
            for psi in self.aux.CB():
                rowv = [0] * len(S)
                for y, val in psi.items():
                    w = self.occupant.get((c, y))
                    if w is not None and w in col: rowv[col[w]] += val
                if keep_zero or any(rowv): out.append(rowv)
        return S, out

# ---------------------------------------------------------------- exact linear algebra (row space membership)
def rank(rows):
    M = [[Fraction(x) for x in r] for r in rows]; rk = 0; ncol = len(M[0]) if M else 0
    for c in range(ncol):
        piv = next((i for i in range(rk, len(M)) if M[i][c] != 0), None)
        if piv is None: continue
        M[rk], M[piv] = M[piv], M[rk]
        for i in range(len(M)):
            if i != rk and M[i][c] != 0:
                fac = M[i][c] / M[rk][c]; M[i] = [a - fac * b for a, b in zip(M[i], M[rk])]
        rk += 1
    return rk

def in_rowspace(rows, vec):
    if not any(vec): return True
    if not rows: return False
    return rank(rows) == rank(rows + [vec])

# ---------------------------------------------------------------- Section 3: the counting routine
class Counter:
    def __init__(self, layout, F, dH=None):
        self.L, self.F = layout, F; aux = layout.aux
        self.Q, self.R = aux.Q, aux.R
        d = sum(len(sc) for (kind, _), sc in zip(layout.factors, layout.scopes) if kind == 'clause')
        self.d = d; self.dH = d * self.R if dH is None else dH                    # deg H <= d R (Definition 3.1: deg P <= R)
        self.q = self.dH // self.Q; self.J = self.q + 1
        self.rowsF = {k: {w: [F.c(c) for c in p] for w, p in layout.P(*k).items()} for k in layout.place}
        self.shifted = {t: {k: [(w, pshift(F, p, t, self.J)) for w, p in row.items()] for k, row in self.rowsF.items()}
                        for t in range(1, self.Q + 1)}
        self._groups = {}

    def phi(self, f, inputs):
        """clause polynomial 1 - prod (1 - L(X)) on truncated-polynomial inputs (dummy factor: 1)"""
        F, J = self.F, self.J; kind, cl = self.L.factors[f]
        if kind == 'dummy': return [F.one()]
        prod = [F.one()]
        for (v, pos), x in zip(cl, inputs):
            lit = x if pos else padd(F, [F.one()], pscale(F, x, F.c(-1)))
            prod = pmul(F, prod, padd(F, [F.one()], pscale(F, lit, F.c(-1))), J)
        return padd(F, [F.one()], pscale(F, prod, F.c(-1)))

    def inputs(self, f, t, x, U):
        """<P_{f,v}(t), x> + <Delta P_{f,v}(z), 1_U> mod z^J for every v in the scope of f"""
        F, J = self.F, self.J; out = []
        for v in self.L.scopes[f]:
            val = [F.zero()] * J
            for w, sh in self.shifted[t][(f, v)]:                             # P(t + z) mod z^J
                if x[w]: val[0] = F.add(val[0], sh[0])
                if w in U:
                    for j in range(1, J): val[j] = F.add(val[j], sh[j])
            out.append(val)
        return out

    def direct_jet(self, t):
        """H(t + z) mod z^J by summing over all x (the check, not the algorithm)"""
        F = self.F; tot = [F.zero()] * self.J; n = self.L.n
        for xi in range(2 ** n):
            x = [(xi >> v) & 1 for v in range(n)]; U = {v for v in range(n) if x[v]}
            prod = [F.one()]
            for f in range(len(self.L.factors)): prod = pmul(F, prod, self.phi(f, self.inputs(f, t, x, U)), self.J)
            tot = padd(F, tot, prod)
        return tot

    def separated_sum(self, t, E, U, literal=False):
        """Lemma 3.2: sum over x with x_i = 1 (i in E) of prod_g A_{g,U}(x; z), by fixing the measurement tuple"""
        F, L = self.F, self.L; r = L.aux.r; n = L.n
        groups = self._groups.get(t) if not literal else None
        if groups is None:
            groups = self._group_tables(t); self._groups[t] = groups
        return self._separated(t, E, U, groups)

    def _group_tables(self, t):
        L = self.L; groups = []
        for g in range(L.aux.r):
            S, C = L.C(t, g); fac = [f for f in range(len(L.factors)) if L.sigma(f, t) == g]
            byy = {}
            for bits in range(2 ** len(S)):
                u = {S[i]: (bits >> i) & 1 for i in range(len(S))}
                y = tuple(sum(cv * u[S[i]] for i, cv in enumerate(row)) for row in C)
                byy.setdefault(y, []).append(u)
            groups.append((S, fac, byy))
        return groups

    def _separated(self, t, E, U, groups):
        F, L = self.F, self.L; n = L.n
        total = [F.zero()] * self.J; tuples = 0
        for ys in itertools.product(*[list(byy) for _, _, byy in groups]):  # realized tuples (the others contribute 0)
            tuples += 1
            reps = [byy[y][0] for (_, _, byy), y in zip(groups, ys)]
            prod = [F.one()]
            for g, ((S, fac, byy), y) in enumerate(zip(groups, ys)):
                base = [0] * n
                for h, rep in enumerate(reps):
                    if h != g:
                        for v, b in rep.items(): base[v] = b
                s = [F.zero()] * self.J
                for u in byy[y]:
                    if any(u[i] != 1 for i in E if i in u): continue
                    x = list(base)
                    for v, b in u.items(): x[v] = b
                    a = [F.one()]
                    for f in fac: a = pmul(F, a, self.phi(f, self.inputs(f, t, x, U)), self.J)
                    s = padd(F, s, a)
                prod = pmul(F, prod, s, self.J)
            total = padd(F, total, prod)
        return total, tuples

    def jet(self, t):
        """H(t + z) mod z^J from Lemma 3.3 (Boolean differences) and Lemma 3.2"""
        F = self.F; n = self.L.n; tot = [F.zero()] * self.J; pairs = 0
        for k in range(min(self.q, n) + 1):
            for E in itertools.combinations(range(n), k):
                for kk in range(k + 1):
                    for U in itertools.combinations(E, kk):
                        z, _ = self.separated_sum(t, set(E), set(U)); pairs += 1
                        sgn = F.c((-1) ** (k - kk)); tot = padd(F, tot, pscale(F, z, sgn))
        return tot, pairs

    def hermite(self, jets):
        """the polynomial of degree < QJ with the given jets at t = 1..Q; returns its coefficients"""
        F, Q, J = self.F, self.Q, self.J; N = Q * J; A = []; b = []
        for t in range(1, Q + 1):
            for j in range(J):
                A.append([F.c(math.comb(k, j) * t ** (k - j)) if k >= j else F.zero() for k in range(N)]); b.append(jets[t - 1][j])
        for c in range(N):                                                    # Gaussian elimination
            piv = next(i for i in range(c, N) if A[i][c] != 0)
            A[c], A[piv] = A[piv], A[c]; b[c], b[piv] = b[piv], b[c]
            iv = F.inv(A[c][c]); A[c] = [F.mul(iv, x) for x in A[c]]; b[c] = F.mul(iv, b[c])
            for i in range(N):
                if i != c and A[i][c] != 0:
                    fac = A[i][c]; A[i] = [F.sub(x, F.mul(fac, y)) for x, y in zip(A[i], A[c])]; b[i] = F.sub(b[i], F.mul(fac, b[c]))
        return b

    def count(self):
        jets = []; pairs = 0
        for t in range(1, self.Q + 1):
            j, p = self.jet(t); jets.append(j); pairs += p
        H = self.hermite(jets)
        return H[0], H, jets, pairs

def as_int(F, x):
    if not F.modular: assert x.denominator == 1; return int(x)
    return x if x <= PRIME // 2 else x - PRIME

# ---------------------------------------------------------------- the verification battery
def check_aux(aux, slow=False):
    """Lemmas 4.1-4.3 exactly, on every label"""
    rep = {'r': aux.r, 'Q': aux.Q, 'R': aux.R, 'A0': aux.A0, 'D': aux.D}
    rep['f_interpolates'] = all(aux.fvals[j] == (-1) ** j for j in aux.I)
    rep['g_vanishes_above_R-1'] = all(aux.g[k] == 0 for k in range(aux.R, aux.Q + 1))
    M0 = aux.M0()
    rep['lemma_4_2_support'] = all(len(aux.E(u, y)) <= aux.R - 1 for u in range(aux.D) for y in M0[u])
    basis = aux.basis(); rep['basis_size'] = len(basis)
    def apply(rows, vec):
        out = {}
        for u, row in enumerate(rows):
            s = sum(c * vec.get(y, 0) for y, c in row.items())
            if s: out[u] = s
        return out
    ok_eig = ok_fix = True
    for j, psi in basis:
        Mpsi = apply(M0, psi); lam = (-1) ** j * aux.fvals[j]
        ok_eig &= Mpsi == {u: lam * v for u, v in psi.items() if lam * v}
        if j in aux.I: ok_fix &= Mpsi == psi
    rep['eigen_relation'] = ok_eig; rep['lemma_4_1_fixes_I_directions'] = ok_fix
    norms = [sum(v * v for v in psi.values()) for _, psi in basis]
    if aux.D <= 4096:
        ok_orth = True
        for i in range(0, len(basis), max(1, len(basis) // 64)):             # a spread sample of pairs, exhaustive for small D
            for k in range(len(basis)):
                if k == i: continue
                pi, pk = basis[i][1], basis[k][1]
                if sum(v * pk.get(u, 0) for u, v in pi.items()): ok_orth = False
        rep['orthogonal_sample'] = ok_orth
    m, p = aux.r * (aux.r - 1) // 2, aux.r * (aux.r + 1) // 2
    cB = sum(math.comb(aux.Q, j) * m ** j * p ** (aux.Q - j) for j in range(aux.Q + 1) if j not in aux.I)
    rep['c_B'] = len(aux.CB()); rep['c_B_formula'] = cB; rep['c_B_matches'] = rep['c_B'] == cB
    # Lemma 4.3: P_u(0) = delta_u, degree <= R-1, and outside the assigned group P_u(t) is a combination of C^B rows
    CB = aux.CB(); ok0 = okdeg = okker = True
    for u in range(aux.D):
        row = aux.row(u)
        ok0 &= {y: p[0] for y, p in row.items() if p[0] != 0} == {u: 1}
        okdeg &= all(len(p) <= aux.R for p in row.values())
        # (I - M0) row u lies in span(C^B) <=> its components on the I-directions vanish
        res = {y: (1 if y == u else 0) - M0[u].get(y, 0) for y in set(M0[u]) | {u}}
        coef = [sum(c * psi.get(y, 0) for y, c in res.items()) for _, psi in basis]
        okker &= all(coef[i] == 0 for i, (j, _) in enumerate(basis) if j in aux.I)
        for t in range(1, aux.Q + 1):                                         # outside d_u(t), P_u(t) equals (I - M0) row u
            du = aux.labels[u][1][t - 1]
            for y, poly in row.items():
                if aux.labels[y][0][t - 1] != du:
                    okker &= peval(Field(False), poly, Fraction(t)) == res.get(y, 0)
    rep['lemma_4_3_P0'] = ok0; rep['lemma_4_3_degree'] = okdeg; rep['lemma_4_3_kernel'] = okker
    dden = math.factorial(aux.R - 1) * math.factorial(aux.Q)
    rep['lemma_4_6_denominator'] = all((dden * c).denominator == 1 for u in range(aux.D) for p in aux.row(u).values() for c in p)
    if slow:                                                                  # M0 by matrix products, against the expansion
        import numpy as np
        D = aux.D; Pi = []
        for s in range(aux.Q):
            P = np.zeros((D, D), dtype=object)
            for u in range(D): P[u, aux.swap(u, [s])] = Fraction(1)
            Pi.append(P)
        Id = np.array([[Fraction(int(i == j)) for j in range(D)] for i in range(D)], dtype=object)
        W = sum((Id - P for P in Pi), np.zeros((D, D), dtype=object)) * Fraction(1, 2)
        fW = np.zeros((D, D), dtype=object); B = Id.copy()
        for j in range(aux.R):
            if j > 0: B = B.dot(W - (aux.A0 + j - 1) * Id) * Fraction(1, j)
            fW = fW + (-1) ** aux.A0 * (-2) ** j * B
        V = Id
        for P in Pi: V = V.dot(P)
        Mslow = V.dot(fW)
        rep['M0_expansion_equals_matrix_product'] = all(Mslow[u, y] == M0[u].get(y, 0) for u in range(D) for y in range(D))
    return rep

def check_remark_4_4():
    """Remark 4.4: r = 2, Q = R = 2, I = {0, 1}, f = 1 - 2z; the row of u = (00, 11) is zeta_0 - (T/2) zeta_1 - T zeta_2"""
    aux = Aux(2, 2, 2, A0=0); u = aux.index[((0, 0), (1, 1))]
    z1 = aux.index[((1, 0), (0, 1))]; z2 = aux.index[((0, 1), (1, 0))]; z12 = aux.index[((1, 1), (0, 0))]
    row = aux.row(u); expect = {u: [1], z1: [0, Fraction(-1, 2)], z2: [0, -1]}
    norm = {y: [c for c in p] for y, p in row.items()}
    for y in norm:
        while len(norm[y]) > 1 and norm[y][-1] == 0: norm[y].pop()
    M0 = aux.M0()[u]
    return {'row_matches': norm == {y: [Fraction(c) for c in p] for y, p in expect.items()},
            'M0_row': {str(aux.labels[y]): str(c) for y, c in M0.items()},
            'M0_is_Pi1+Pi2-Pi1Pi2': M0 == {z1: 1, z2: 1, z12: -1}}

def check_layout(L):
    """Definition 3.1 (1)-(5) on the actual variables, exactly"""
    aux, n = L.aux, L.n; rep = {'n': n, 'factors': len(L.factors), 'h': L.h, 'incidences': len(L.place)}
    ok0 = okdeg = okker = True; rows_total = []; maxabs = 0
    for t in range(1, aux.Q + 1):
        Cs = {g: L.C(t, g) for g in range(aux.r)}
        rows_total.append(sum(len(C) for _, C in Cs.values()))
        maxabs = max([maxabs] + [sum(abs(x) for x in row) for _, C in Cs.values() for row in C])
        for (f, v) in L.place:
            P = L.P(f, v); g0 = L.sigma(f, t)
            for g in range(aux.r):
                if g == g0: continue
                S, C = Cs[g]
                vec = [peval(Field(False), P[w], Fraction(t)) if w in P else 0 for w in S]
                if S: okker &= in_rowspace(C, vec)
    for (f, v) in L.place:
        P = L.P(f, v)
        ok0 &= {w: p[0] for w, p in P.items() if p[0] != 0} == {v: 1}
        okdeg &= all(len(p) <= aux.R for p in P.values())
    rep.update({'P0_is_delta': ok0, 'degree_le_R-1': okdeg, 'kernel_condition': okker,
                'nonzero_measurement_rows_per_point': rows_total, 'max_abs_row_sum': maxabs, 'row_sum_le_D': maxabs <= aux.D,
                'group_sizes': [[len(L.group(t, g)) for g in range(aux.r)] for t in range(1, aux.Q + 1)]})
    return rep

def check_count(r, Q, R, n, m, seed, modular=True, direct=True):
    rng = random.Random(seed); clauses = random_bounded_3cnf(n, m, rng)
    aux = Aux(r, Q, R); L = Layout(aux, n, clauses, seed); F = Field(modular); Cn = Counter(L, F)
    t0 = time.time(); val, H, jets, pairs = Cn.count(); secs = time.time() - t0
    truth = brute_count(n, clauses)
    rep = {'r': r, 'Q': Q, 'R': R, 'n': n, 'clauses': len(clauses), 'seed': seed, 'field': 'GF(2^61-1)' if modular else 'Q',
           'd': Cn.d, 'd_H': Cn.dH, 'q': Cn.q, 'J': Cn.J, 'pairs_U_subset_E': pairs, 'count_algorithm': as_int(F, val),
           'count_brute_force': truth, 'equal': as_int(F, val) == truth, 'seconds': round(secs, 2),
           'H_degree_le_dH': all(c == 0 for c in H[Cn.dH + 1:])}
    if direct:                                                                # the jets against direct summation over all x
        rep['jets_equal_direct'] = all(jets[t - 1] == Cn.direct_jet(t) for t in range(1, Q + 1))
    return rep

def check_adversarial(r, Q, R, n, m, seed):
    """break the design at t = 1 and confirm that the break is detected: (a) the kernel condition of Definition 3.1 fails for a
    clause incidence and (b) the separated sum then differs from H(1).  Variants: every row removed; the first single row whose
    removal breaks the kernel condition for some clause incidence.  (Dummy factors are constant, so their incidences are skipped.)"""
    rng = random.Random(seed); clauses = random_bounded_3cnf(n, m, rng)
    aux = Aux(r, Q, R); L = Layout(aux, n, clauses, seed); F = Field(True); Cn = Counter(L, F)
    good, _ = Cn.separated_sum(1, set(), set()); direct = Cn.direct_jet(1)
    out = {'formula': clauses, 'separated_equals_direct': good[0] == direct[0]}
    orig = L.C
    clause_inc = [(f, v) for (f, v) in L.place if L.factors[f][0] == 'clause']
    def kernel_ok(Cfun):
        for (f, v) in clause_inc:
            P = L.P(f, v)
            for g in range(aux.r):
                if g == L.sigma(f, 1): continue
                S, C = Cfun(1, g)
                vec = [peval(Field(False), P[w], Fraction(1)) if w in P else 0 for w in S]
                if S and not in_rowspace(C, vec): return False
        return True
    def run(mod):
        def broken(t, g, keep_zero=False):
            S, C = orig(t, g, keep_zero)
            return mod(g, S, C) if t == 1 else (S, C)
        L.C = broken; Cn._groups = {}
        ker = kernel_ok(L.C); bad, _ = Cn.separated_sum(1, set(), set())
        L.C = orig; Cn._groups = {}
        return {'kernel_condition_holds': ker, 'separated_equals_direct': bad[0] == direct[0]}
    out['all_rows_removed'] = run(lambda g, S, C: (S, []))
    found = None
    for g in range(aux.r):
        S, C = orig(1, g)
        for i in range(len(C)):
            res = run(lambda gg, SS, CC, g=g, i=i: (SS, CC[:i] + CC[i + 1:]) if gg == g else (SS, CC))
            if not res['kernel_condition_holds']: found = {'group': g, 'row': i, **res}; break
        if found: break
    out['one_essential_row_removed'] = found or 'no single row is essential'
    return out

if __name__ == '__main__':
    out = {'source': 'openai/math 7ef5c0cc5, preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/build/main_full_version.tex'}
    out['remark_4_4'] = check_remark_4_4(); print('remark 4.4', out['remark_4_4'], flush=True)
    out['aux'] = []
    for (r, Q, R, slow) in [(2, 2, 2, True), (2, 3, 2, True), (2, 4, 2, False), (2, 4, 3, False), (3, 2, 1, True), (3, 3, 2, False), (2, 5, 3, False)]:
        rep = check_aux(Aux(r, Q, R), slow); out['aux'].append(rep); print('aux', rep, flush=True)
    out['layout'] = []
    for (r, Q, R, n, m, seed) in [(2, 3, 2, 6, 4, 1), (2, 4, 2, 7, 5, 2), (3, 3, 2, 6, 4, 3)]:
        rng = random.Random(seed); cl = random_bounded_3cnf(n, m, rng)
        rep = check_layout(Layout(Aux(r, Q, R), n, cl, seed)); rep.update({'r': r, 'Q': Q, 'R': R}); out['layout'].append(rep); print('layout', rep, flush=True)
    out['count'] = []
    for args in [(2, 3, 2, 4, 2, 11, False), (2, 3, 2, 5, 3, 12, True), (2, 4, 2, 6, 3, 13, True), (2, 3, 2, 5, 4, 14, True),
                 (3, 3, 2, 5, 3, 15, True), (2, 4, 3, 5, 3, 16, True), (2, 5, 2, 7, 3, 17, True), (2, 4, 2, 6, 4, 18, False)]:
        r, Q, R, n, m, seed, mod = args
        rep = check_count(r, Q, R, n, m, seed, modular=mod); out['count'].append(rep); print('count', rep, flush=True)
    out['adversarial'] = [check_adversarial(2, 3, 2, 6, 4, sd) for sd in (21, 22, 23, 24)] + [check_adversarial(3, 3, 2, 5, 3, 25)]
    print('adversarial', out['adversarial'], flush=True)
    json.dump(out, open(os.path.join(RES, 'phase13_eth.json'), 'w'), indent=1, default=str)
