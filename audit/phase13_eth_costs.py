#!/usr/bin/env python3
"""Phase XIII: where can the counting algorithm of "The Exponential Time Hypothesis is False" (openai/math, Family 378) beat 2^n?

Everything here is computed from the paper's own statements (main_full_version.tex) and the Lean schedule's definitions.
1. The explicit schedule of Lemma 4.8 / Section 5:  lambda = ceil(log2 n), nu = ceil(log2 lambda),
   r = floor(sqrt(lambda)/nu^2), Q = floor(lambda/(128 nu)), R = (beta+3) ceil(sqrt(lambda)), tau = 1/(r lambda), D = r^(2Q).
   The algorithm falls back to checking all 2^n assignments unless r >= 2, Q > R, R >= 32, 6R <= Q, the interval lies in
   {0..Q}, the two balance inequalities and the tail bound hold (Section 5, "If any check fails ...").  We find the least lambda
   for which the integer guards pass; the others (balance, tail) then hold by the paper's own estimates (checked here too).
2. At that lambda, the paper's bound of Proposition 3.4, 2Qr C_q (2D+1)^(2 tau n) 2^(2n/r), relative to 2^n.
3. A free search: every (r, Q, R), interval chosen as in Lemma 4.8, tau the least value allowed by the tail condition
   (tau = r b Pr[W not in I]) and the balance hypothesis 2(b+w)D^2 <= M <= 3n of Lemma 4.5 (b = w = 3, the bounded-occurrence
   3-CNF of Section 2).  Least n at which Proposition 3.4's bound is below 2^n.
4. The Lean schedule (lean/OAI/Algorithms/SubexponentialSAT/SubexpPackingParameters.lean): s n = log2 (log2 n), and every
   main-branch input satisfies GoodInput n := 32 <= s n, i.e. n >= 2^(2^32).
Taylor cost: log2 C_q = log2 sum_{j<=q} 2^j binom(n, j), q = floor(d R / Q); for n -> infinity with q/n -> alpha <= 2/3 this is
n (alpha + H2(alpha)) + O(log n); d = delta n with delta = 1 (most favourable) and delta = 3 (M = 3n).
Usage: python -u -I audit/phase13_eth_costs.py -> audit/results/phase13_eth_costs.json"""
import math, json, os
from fractions import Fraction
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__)); RES = os.path.join(HERE, 'results')

def ceil_log2(x):  return (x - 1).bit_length()                # least L with x <= 2^L, for x >= 1
def ceil_sqrt(x):
    s = math.isqrt(x); return s if s * s == x else s + 1
def H2(a): return 0.0 if a <= 0 or a >= 1 else -(a * math.log2(a) + (1 - a) * math.log2(1 - a))
def taylor_rate(alpha): return math.log2(3) if alpha >= 2 / 3 else alpha + H2(alpha)

def explicit(lam, beta=1):
    nu = ceil_log2(lam); r = math.isqrt(lam // nu ** 4); Q = lam // (128 * nu); R = (beta + 3) * ceil_sqrt(lam)
    return nu, r, Q, R

def guards(lam, beta=1):
    nu, r, Q, R = explicit(lam, beta)
    return r >= 2 and Q > R and R >= 32 and 6 * R <= Q

def least_lambda(beta=1):
    """least lambda (= ceil(log2 n)) passing the integer guards; within a block of equal nu the guards are monotone in lambda"""
    for nu in range(1, 80):
        lo, hi = 2 ** (nu - 1) + 1, 2 ** nu
        if nu == 1: lo = 1
        if not guards(hi, beta): continue
        while lo < hi:
            mid = (lo + hi) // 2
            if guards(mid, beta): hi = mid
            else: lo = mid + 1
        assert guards(lo, beta) and all(not guards(x, beta) for x in range(max(1, lo - 2000), lo))
        return lo
    return None

def log_binom_pmf(Q, p):
    from scipy.special import gammaln
    j = np.arange(Q + 1, dtype=float)
    return gammaln(Q + 1) - gammaln(j + 1) - gammaln(Q - j + 1) + j * math.log(p) + (Q - j) * math.log1p(-p)

def tails(Q, r):
    """for every R in 1..Q: Pr[W not in I_R] with the interval of Lemma 4.8, A0 = floor(Q(r-1)/(2r) - (R-1)/2)"""
    p = (r - 1) / (2 * r); lp = log_binom_pmf(Q, p); pmf = np.exp(lp - lp.max()); pmf /= pmf.sum()
    left = np.concatenate([[0.0], np.cumsum(pmf)])            # left[a] = Pr[W < a]
    right = np.concatenate([np.cumsum(pmf[::-1])[::-1], [0.0]])   # right[b] = Pr[W >= b]
    out = {}
    for R in range(1, Q + 1):
        A0 = math.floor(Fraction(Q * (r - 1), 2 * r) - Fraction(R - 1, 2))
        if A0 < 0 or A0 + R - 1 > Q: continue
        out[R] = (A0, float(left[A0] + right[A0 + R]))
    return out

def exact_tail(Q, r, A0, R):
    m, p = r * (r - 1) // 2, r * (r + 1) // 2
    num = sum(math.comb(Q, j) * m ** j * p ** (Q - j) for j in range(Q + 1) if not (A0 <= j < A0 + R))
    return Fraction(num, r ** (2 * Q))

def rate(r, Q, R, tail, delta, b=3):
    """exponent / n of Proposition 3.4's bound, n -> infinity at fixed parameters: Taylor + measurements + one group"""
    alpha = delta * R / Q; tau = r * b * tail; D_log2 = 2 * Q * math.log2(r)
    meas = 2 * tau * (D_log2 + 1)                               # log2(2D+1) <= log2 D + 1
    return taylor_rate(alpha) + meas + 2 / r, {'taylor': taylor_rate(alpha), 'measurements': meas, 'group': 2 / r, 'tau': tau}

def best_R(r, Q, delta):
    """the R minimising the rate at fixed (r, Q): a scan of R = 1..Q-1 (vectorised)"""
    p = (r - 1) / (2 * r); lp = log_binom_pmf(Q, p); pmf = np.exp(lp - lp.max()); pmf /= pmf.sum()
    left = np.concatenate([[0.0], np.cumsum(pmf)]); right = np.concatenate([np.cumsum(pmf[::-1])[::-1], [0.0]])
    R = np.arange(1, Q)
    A0 = np.floor(Q * (r - 1) / (2 * r) - (R - 1) / 2).astype(np.int64)
    ok = (A0 >= 0) & (A0 + R - 1 <= Q)
    R, A0 = R[ok], A0[ok]
    tail = left[A0] + right[A0 + R]
    alpha = delta * R / Q
    with np.errstate(divide='ignore', invalid='ignore'):
        h2 = np.where((alpha > 0) & (alpha < 1), -(alpha * np.log2(alpha) + (1 - alpha) * np.log2(1 - alpha)), 0.0)
    tay = np.where(alpha >= 2 / 3, math.log2(3), alpha + h2)
    meas = 2 * r * 3 * tail * (2 * Q * math.log2(r) + 1)
    e = tay + meas + 2 / r
    k = int(np.argmin(e)); return float(e[k]), int(R[k]), int(A0[k]), float(tail[k])

def free_search(delta, r_max=64):
    """least log2 n over r in 3..r_max of the least Q with min_R rate < 1 (exponential then binary search in Q; the feasible set
    in Q is checked to be an up-set on the bracketing interval)"""
    best = None; per_r = {}
    for r in range(3, r_max + 1):
        if 2 / r >= 1: continue
        hi = 4
        while best_R(r, hi, delta)[0] >= 1:
            hi *= 2
            if hi > 2 ** 17: break
        if hi > 2 ** 17: continue
        lo = hi // 2
        while lo + 1 < hi:
            mid = (lo + hi) // 2
            if best_R(r, mid, delta)[0] < 1: hi = mid
            else: lo = mid
        Q = hi; e, R, A0, tail = best_R(r, Q, delta)
        upset = all(best_R(r, q, delta)[0] < 1 for q in range(Q, min(2 * Q, Q + 40)))
        log2_N = 2 + 4 * Q * math.log2(r); per_r[r] = {'Q': Q, 'log2_n_min': log2_N, 'up_set_checked': upset}
        if best is None or log2_N < best['log2_n_min']:
            best = {'r': r, 'Q': Q, 'R': R, 'A0': A0, 'tail_float': tail, 'rate': e, 'log2_n_min': log2_N, 'up_set_checked': upset}
    t = exact_tail(best['Q'], best['r'], best['A0'], best['R']); best['tail_exact_float'] = float(t)
    best['rate_with_exact_tail'], best['parts'] = rate(best['r'], best['Q'], best['R'], float(t), delta)
    best['per_r'] = per_r
    # exhaustive confirmation: no (r, Q) with a smaller n-threshold is feasible (only Q < (best - 2)/(4 log2 r) can improve it)
    improving = []
    for r in range(3, r_max + 1):
        cap = int((best['log2_n_min'] - 2) / (4 * math.log2(r)))
        for Q in range(2, cap + 1):
            if 2 + 4 * Q * math.log2(r) >= best['log2_n_min']: break
            if best_R(r, Q, delta)[0] < 1: improving.append((r, Q))
    best['exhaustive_check_r_range'] = [3, r_max]; best['improving_found'] = improving
    return best

if __name__ == '__main__':
    out = {'source': 'openai/math 7ef5c0cc5: main_full_version.tex Lemma 4.8, Section 5, Proposition 3.4; '
                     'lean/OAI/Algorithms/SubexponentialSAT/SubexpPackingParameters.lean'}
    ex = {}
    for beta in (1, 2, 3):
        lam = least_lambda(beta); nu, r, Q, R = explicit(lam, beta)
        D_log2 = 2 * Q * math.log2(r); tau = 1 / (r * lam)
        hoeff = -R * R / (8 * Q) * math.log2(math.e) + 1           # log2 of 2 exp(-R^2/(8Q))
        rec = {'least_lambda': lam, 'log10_lambda': math.log10(lam), 'nu': nu, 'r': r, 'Q': Q, 'R': R, 'log2_D': D_log2,
               'log2_n_lower': lam - 1, 'balance_ok_by_log2D_le_lambda_over_128': D_log2 <= lam / 128,
               'tail_hoeffding_log2': hoeff, 'tail_required_log2 (b = lambda^beta)': -math.log2(lam ** beta * r * r * lam),
               'tail_ok': hoeff <= -math.log2(lam ** beta * r * r * lam)}
        for delta in (1, 3):
            alpha = delta * R / Q; meas = 2 * tau * (D_log2 + 1)
            rec[f'rate_delta{delta}'] = {'taylor': taylor_rate(alpha), 'alpha': alpha, 'measurements': meas, 'group': 2 / r,
                                         'total': taylor_rate(alpha) + meas + 2 / r}
        ex[beta] = rec; print('explicit beta', beta, rec, flush=True)
    out['explicit_schedule'] = ex
    # where the explicit schedule's bound first drops below 2^n (beta = 1): scan lambda upward in factors of 2^(1/8)
    first = {}
    for delta in (1, 3):
        lam = ex[1]['least_lambda']
        while True:
            nu, r, Q, R = explicit(lam)
            if guards(lam):
                tau = 1 / (r * lam); e = taylor_rate(delta * R / Q) + 2 * tau * (2 * Q * math.log2(r) + 1) + 2 / r
                if e < 1: first[delta] = {'lambda': lam, 'log10_lambda': math.log10(lam), 'rate': e, 'r': r, 'Q': Q, 'R': R}; break
            lam = int(lam * 2 ** 0.125) + 1
    out['explicit_schedule_bound_below_2^n'] = first; print('explicit, bound < 2^n from', first, flush=True)
    out['free_search'] = {}
    for delta in (1, 3):
        b = free_search(delta); out['free_search'][delta] = b; print('free search delta', delta, b, flush=True)
    out['lean_goodinput'] = {'definition': 'GoodInput n := 32 <= Nat.log2 (Nat.log2 n)', 'least_n': '2^(2^32)',
                             'log10_least_n': 2 ** 32 * math.log10(2)}
    json.dump(out, open(os.path.join(RES, 'phase13_eth_costs.json'), 'w'), indent=1)
