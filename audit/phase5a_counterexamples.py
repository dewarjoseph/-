"""
phase5a_counterexamples.py -- exact (sympy) counterexamples delimiting the general theorem behind the FR30 type
recursion.  Each example is a substitution on a finite alphabet with its substitution matrix in the SAME convention
as the FR30 operator S:  Mat[r, c] = number of letters (or k-blocks) of type r in the image of one letter of type c,
so columns are indexed by the parent type and count vectors are columns, v_{n+1} = Mat v_n.

Run from the repository root:  python3 -u -I audit/phase5a_counterexamples.py
Output: audit/results/phase5a_counterexamples.txt

  (a) Fibonacci  a -> ab, b -> a.    Finite type (2 letters), exact linear recursion, primitive, but NON-constant
      length: the Perron root is phi = (1+sqrt5)/2 and the limiting letter frequencies are 1/phi, 1/phi^2, IRRATIONAL.
      Refutes:  'finite type + exact recursion  =>  rational limiting frequencies'.
      Rationality needs an INTEGER Perron root, which constant length (every image has the same length L, hence
      constant column sums L) provides.
  (b) a -> aa, b -> bb.   Constant length 2 but NOT primitive (reducible: two sink components {a}, {b}).  Limiting
      frequencies exist for every seed but equal the SEED frequencies, so they are seed-dependent.
      Refutes:  'constant length + finite type  =>  seed-independent limiting frequencies'.
      For the FR30 supertile recursion v_{m+1} = S v_m + 8^m f the limit is nevertheless seed-independent, because the
      forcing eigenvalue 8 strictly dominates rho(S) = 4: v_m/8^m -> (8 - S)^{-1} f for EVERY initial vector v_1.
      This is demonstrated on a toy affine recursion with the matrix of (b) as S.
  (c) Thue-Morse  0 -> 01, 1 -> 10.  Constant length 2, primitive, letter matrix [[1,1],[1,1]] with spectrum {2, 0}
      (clean).  The induced substitution on 2-blocks (the analogue of passing from tiles to panels/plaquettes) has
      a 4x4 matrix whose spectrum is computed exactly below; the frequencies of 2-blocks are rational.
      Whatever the 2-block spectrum turns out to be, the statement tested is: 'clean letter spectrum  =>  clean
      induced (collared) spectrum'.
  (d) Period-doubling  0 -> 01, 1 -> 00.  Constant length 2, primitive, letter matrix [[1,2],[1,0]] with spectrum
      {2, -1}: NON-clean already at the letter level, yet the frequencies (2/3, 1/3) are rational and the finite-size
      corrections carry the factor (-1)^n (an exact oscillation, not a decay).
      Refutes:  'rational frequencies  =>  clean spectrum'  and  'constant length  =>  clean spectrum'.
"""
import os, sys, collections
import sympy as sp

HERE = os.path.dirname(os.path.abspath(__file__))
lam = sp.Symbol('lambda')

def subst_matrix(rule, alphabet):
    """Mat[r, c] = number of occurrences of letter alphabet[r] in rule[alphabet[c]] (columns = parents)."""
    n = len(alphabet); idx = {a: i for i, a in enumerate(alphabet)}
    Mat = sp.zeros(n, n)
    for c, a in enumerate(alphabet):
        for x in rule[a]: Mat[idx[x], c] += 1
    return Mat

def iterate_word(rule, seed, n):
    w = seed
    for _ in range(n): w = ''.join(rule[x] for x in w)
    return w

def letter_counts(word, alphabet):
    cnt = collections.Counter(word); return sp.Matrix([cnt.get(a, 0) for a in alphabet])

def block_rule(rule, k=2):
    """Induced substitution on k-blocks for a constant-length-L rule: the block w = w_0..w_{k-1} maps to the L blocks
    of length k starting at positions 0..L-1 of sigma(w) (Queffelec's k-block presentation).  Returns (rule, alphabet)
    on the legal k-blocks (those occurring in the fixed point / all blocks reachable from the letters' images)."""
    L = {len(v) for v in rule.values()}; assert len(L) == 1, 'constant length required'; L = L.pop()
    def img(w):
        s = ''.join(rule[x] for x in w); return [s[i:i + k] for i in range(L)]
    # legal blocks: close under the induced map starting from all k-blocks inside sigma^2 of each letter
    legal = set()
    for a in rule:
        w = iterate_word(rule, a, 2)
        legal |= {w[i:i + k] for i in range(len(w) - k + 1)}
    changed = True
    while changed:
        changed = False
        for b in list(legal):
            for bb in img(b):
                if bb not in legal: legal.add(bb); changed = True
    alphabet = sorted(legal)
    return {b: img(b) for b in alphabet}, alphabet

def perron_data(Mat):
    cp = Mat.charpoly(lam).as_expr()
    ev = Mat.eigenvals()
    rho = max(ev, key=lambda z: abs(complex(z)))
    vec = (Mat - rho * sp.eye(Mat.shape[0])).nullspace()
    assert len(vec) == 1
    u = vec[0]; u = sp.simplify(u / sum(u))
    return cp, ev, rho, u

def report(title, lines, out):
    print(f"\n{title}"); out.write(f"\n{title}\n")
    for l in lines: print(" " + l); out.write(" " + l + "\n")

def example_a(out):
    rule = {'a': 'ab', 'b': 'a'}; alph = ['a', 'b']; Mat = subst_matrix(rule, alph)
    cp, ev, rho, u = perron_data(Mat)
    phi = (1 + sp.sqrt(5)) / 2
    exact = [sp.simplify(u[0] - 1 / phi) == 0, sp.simplify(u[1] - 1 / phi**2) == 0]
    irr = [not u[i].is_rational for i in range(2)]
    # finite iterates: counts from the seed 'a' obey v_{n+1} = Mat v_n exactly
    rec_ok = True; v = letter_counts('a', alph)
    for n in range(1, 13):
        w = iterate_word(rule, 'a', n); v = Mat * v
        rec_ok &= (letter_counts(w, alph) == v)
    lines = [f"rule {rule}; matrix (columns = parents) {Mat.tolist()}; column sums {[sum(Mat[:, j]) for j in range(2)]} (NOT constant -> not constant length)",
             f"charpoly {sp.factor(cp)}; eigenvalues {ev}; Perron root {sp.nsimplify(rho)} = phi: {sp.simplify(rho - phi) == 0}",
             f"exact recursion v_(n+1) = Mat v_n reproduces the letter counts of sigma^n(a) for n = 1..12: {rec_ok}",
             f"normalized Perron vector (limiting letter frequencies) = {list(u)} = (1/phi, 1/phi^2): {all(exact)}; irrational: {all(irr)}",
             "VERDICT: finite type + exact recursion + primitivity do NOT imply rational frequencies; the integer Perron root (constant length) is needed."]
    report("(a) Fibonacci a->ab, b->a", lines, out)
    return dict(cp=cp, u=list(u), irrational=all(irr), rec_ok=rec_ok)

def example_b(out):
    rule = {'a': 'aa', 'b': 'bb'}; alph = ['a', 'b']; Mat = subst_matrix(rule, alph)
    cp = Mat.charpoly(lam).as_expr()
    res = {}
    for seed in ('a', 'b', 'ab', 'aab'):
        v = letter_counts(seed, alph); vn = Mat**10 * v
        res[seed] = [sp.Rational(x, sum(vn)) for x in vn]
    seed_dep = len({tuple(r) for r in res.values()}) > 1
    # primitivity check: Mat^k has a zero entry for every k
    prim = any(all(x > 0 for x in Mat**k) for k in range(1, 5))
    # contrast: affine recursion with the SAME non-primitive matrix and dominant forcing 8^m f
    f = sp.Matrix([1, 2]); lim = (8 * sp.eye(2) - Mat).inv() * f
    # exact limit: v_m / 8^m = (8-S)^{-1} f + O((2/8)^m); the deviation shrinks geometrically for every seed v_1
    def dev(v1, m):
        v = v1                                   # v = v_1
        for j in range(1, m): v = Mat * v + 8**j * f   # v_{j+1} = Mat v_j + 8^j f  ->  v = v_m
        return [abs(x) for x in (v / sp.Integer(8)**m - lim)]
    devs = {str(list(v1)): [dev(v1, m) for m in (5, 10, 20)] for v1 in (sp.Matrix([1, 0]), sp.Matrix([0, 1]), sp.Matrix([5, 7]))}
    ratio_ok = all(d[1][i] * 4**5 == d[0][i] and d[2][i] * 4**10 == d[1][i] for d in devs.values() for i in range(2))
    lines = [f"rule {rule}; matrix {Mat.tolist()}; column sums {[sum(Mat[:, j]) for j in range(2)]} (constant length 2); charpoly {sp.factor(cp)}",
             f"primitive (some power strictly positive): {prim}; sink components: {{a}}, {{b}} (two sinks -> eigenvalue 2 has multiplicity 2)",
             f"normalized counts after 10 inflations, by seed: {res}  -> seed-dependent: {seed_dep}",
             f"CONTRAST (forced recursion v_(m+1) = Mat v_m + 8^m f, f = {list(f)}, v_1 = seed): (8 - Mat)^(-1) f = {list(lim)}; deviations |v_m/8^m - lim| at m = 5, 10, 20 for seeds (1,0), (0,1), (5,7): {devs}",
             f"  deviations decay by the exact factor (2/8)^5 = 4^(-5) per 5 levels (here exactly 4^(-m) (v_1/2 - 2f/3)): {ratio_ok}  -> the forced limit is seed-independent without primitivity because 8 > rho(Mat) = 2.",
             "VERDICT: for a HOMOGENEOUS recursion, seed-independence of the limit needs primitivity (or at least a unique sink component);",
             "         for the FR30 supertile recursion it follows instead from the dominant forcing eigenvalue 8 > rho(S) = 4."]
    report("(b) non-primitive a->aa, b->bb", lines, out)
    return dict(cp=cp, seed_dependent=seed_dep, primitive=prim, forced_limit=list(lim), ratio_ok=ratio_ok)

def example_c(out):
    rule = {'0': '01', '1': '10'}; alph = ['0', '1']; Mat = subst_matrix(rule, alph)
    cp1, ev1, rho1, u1 = perron_data(Mat)
    rule2, alph2 = block_rule(rule, 2); Mat2 = subst_matrix(rule2, alph2)
    cp2, ev2, rho2, u2 = perron_data(Mat2)
    clean1 = all(f in (lam, lam - 2, lam - 1) for f, _ in sp.factor_list(cp1, lam)[1])
    clean2 = all(f in (lam, lam - 2, lam - 1) for f, _ in sp.factor_list(cp2, lam)[1])
    # check the 2-block frequencies against a long prefix of the fixed point
    w = iterate_word(rule, '0', 14); n = len(w) - 1
    emp = collections.Counter(w[i:i + 2] for i in range(n))
    emp_fr = [sp.Rational(emp[b], n) for b in alph2]
    # exact finite-size law: v_n = Mat2^n v_0 decomposed along eigenvalues; show the (-1)^n or other components
    P, J = Mat2.jordan_form()
    lines = [f"letter rule {rule}; letter matrix {Mat.tolist()}; charpoly {sp.factor(cp1)}; eigenvalues {ev1}; clean (nonzero spec in {{2,1}}): {clean1}; letter frequencies {list(u1)}",
             f"2-block alphabet {alph2}; induced rule {rule2}",
             f"2-block matrix (columns = parent blocks) {Mat2.tolist()}; column sums {[sum(Mat2[:, j]) for j in range(len(alph2))]}",
             f"2-block charpoly {sp.factor(cp2)}; eigenvalues {ev2}; clean (nonzero spec in {{2,1}}): {clean2}",
             f"Jordan form diagonal {list(J.diagonal())} (semisimple: {J.is_diagonal()})",
             f"2-block limiting frequencies (normalized Perron vector) {list(u2)}; rational: {all(x.is_rational for x in u2)}; empirical on sigma^14(0) ({n} blocks): {emp_fr}",
             f"VERDICT: letter spectrum clean = {clean1}, induced 2-block spectrum clean = {clean2}; see the deliverable for the reading."]
    report("(c) Thue-Morse 0->01, 1->10 and its 2-block substitution", lines, out)
    return dict(cp1=cp1, cp2=cp2, clean1=clean1, clean2=clean2, u2=list(u2), alph2=alph2, Mat2=Mat2.tolist(), ev2=ev2)

def example_d(out):
    rule = {'0': '01', '1': '00'}; alph = ['0', '1']; Mat = subst_matrix(rule, alph)
    cp, ev, rho, u = perron_data(Mat)
    clean = all(f in (lam, lam - 2, lam - 1) for f, _ in sp.factor_list(cp, lam)[1])
    # exact closed form of the counts from seed '0': v_n = a 2^n + b (-1)^n  (two simple eigenvalues)
    v0 = letter_counts('0', alph); P, Dg = Mat.diagonalize(); coeff = P.inv() * v0
    closed = {n: list(P * sp.diag(*[d**n for d in Dg.diagonal()]) * coeff) for n in range(0, 7)}
    direct = {n: list(letter_counts(iterate_word(rule, '0', n), alph)) for n in range(0, 7)}
    cf_ok = all(closed[n] == direct[n] for n in closed)
    lines = [f"rule {rule}; matrix {Mat.tolist()}; column sums {[sum(Mat[:, j]) for j in range(2)]} (constant length 2, primitive: {all(x > 0 for x in Mat**2)})",
             f"charpoly {sp.factor(cp)}; eigenvalues {ev}; clean: {clean}; limiting frequencies {list(u)}; rational: {all(x.is_rational for x in u)}",
             f"exact closed form v_n = P diag(2^n, (-1)^n) P^-1 v_0 equals the direct counts of sigma^n(0) for n = 0..6: {cf_ok}; e.g. v_n = {closed[6]} at n = 6; coefficient vector along (2^n, (-1)^n): {list(coeff)}",
             "VERDICT: constant length and primitivity give rational frequencies even though the spectrum is NOT clean; the non-clean eigenvalue -1 produces an exact (-1)^n oscillation in the finite-size corrections."]
    report("(d) period-doubling 0->01, 1->00", lines, out)
    return dict(cp=cp, clean=clean, u=list(u), cf_ok=cf_ok)

def main():
    os.makedirs(os.path.join(HERE, 'results'), exist_ok=True)
    out = open(os.path.join(HERE, 'results', 'phase5a_counterexamples.txt'), 'w')
    out.write(f"phase5a_counterexamples.py  sympy {sp.__version__}\n")
    ra, rb, rc, rd = example_a(out), example_b(out), example_c(out), example_d(out)
    out.close()
    return ra, rb, rc, rd

if __name__ == '__main__':
    main()
