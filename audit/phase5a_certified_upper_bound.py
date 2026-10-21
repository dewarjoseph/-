"""
Phase 5a / Task B3: CERTIFIED upper bounds on E_bulk = inf spec(H_omega) for the pinned Clifford operator.

For every m, lambda_min(H^pin_m) >= E_bulk (compression theorem), and for ANY vector psi,
    E_bulk <= lambda_min(H^pin_m) <= <psi, H^pin_m psi> / <psi, psi>.
We take the LOBPCG approximate ground state, round it to a Gaussian-integer vector (scale 2^S), and evaluate the
Rayleigh quotient EXACTLY with Python integers: H^pin_m = 24 - A with A built from Q8 links whose entries are in
{0, +-1, +-i}, so <psi, H psi> and <psi, psi> are integers.  The resulting rational number is a rigorous upper bound
for lambda_min(H^pin_m), hence for E_bulk, independent of floating-point error.  Levels 2..5.

Run from the repository root:  python3 -u -I audit/phase5a_certified_upper_bound.py [maxlevel]
"""
import os, sys, time, collections
from fractions import Fraction
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np, scipy.sparse as sps, scipy.sparse.linalg as spl
from independent_clifford_q8_audit import FR30, tiles_at_level, panel_edges, clifford_link

maxlvl = int(sys.argv[1]) if len(sys.argv) > 1 else 5
SCALE = 2 ** 24
OUT = []
def say(s): print(s, flush=True); OUT.append(s)

def gauss_int(C):
    """2x2 complex matrix with entries in {0,+-1,+-i} -> integer pairs (re, im)."""
    M = np.rint(np.stack([C.real, C.imag], axis=-1)).astype(int)
    assert np.allclose(M[..., 0] + 1j * M[..., 1], C, atol=1e-12)
    return [[(int(M[r, c, 0]), int(M[r, c, 1])) for c in range(2)] for r in range(2)]

def build(lvl):
    tiles = tiles_at_level(FR30, lvl); owner, edges = panel_edges(tiles); n = len(tiles)
    links = []
    rows, cols, vals = [], [], []
    for a in range(n):
        for r in range(2): rows.append(2 * a + r); cols.append(2 * a + r); vals.append(24.0)
    for (a, b, nf, _, _) in edges:
        C = clifford_link(tiles[a][0], tiles[b][0], nf); links.append((a, b, gauss_int(C)))
        for r in range(2):
            for c in range(2): rows += [2 * a + r, 2 * b + c]; cols += [2 * b + c, 2 * a + r]; vals += [-C[r, c], -np.conj(C[r, c])]
    H = sps.coo_matrix((vals, (rows, cols)), shape=(2 * n, 2 * n)).tocsr()
    return H, n, links

def lowest(H, k=4, seed=0, maxiter=4000, tol=1e-8):
    rng = np.random.default_rng(seed); N = H.shape[0]
    X = rng.standard_normal((N, k)) + 1j * rng.standard_normal((N, k))
    dinv = 1.0 / H.diagonal().real
    M = spl.LinearOperator(H.shape, matvec=lambda v: dinv * v, dtype=complex)
    w, V = spl.lobpcg(H, X, M=M, largest=False, tol=tol, maxiter=maxiter)
    o = np.argsort(w.real); return w.real[o], V[:, o]

def exact_rayleigh(psi, n, links):
    """psi: complex vector of length 2n (float). Returns Fraction <p,Hp>/<p,p> for p = round(SCALE*psi), exactly."""
    P = np.rint(psi * SCALE)
    pr = [int(x) for x in P.real]; pi = [int(x) for x in P.imag]
    norm2 = sum(pr[i] * pr[i] + pi[i] * pi[i] for i in range(2 * n))
    diag = 24 * norm2
    # <p, A p> = sum_f [ <p_a, C_f p_b> + <p_b, C_f^dag p_a> ] = 2 Re sum_f <p_a, C_f p_b>
    re_sum = 0
    for a, b, C in links:
        for r in range(2):
            ar, ai = pr[2 * a + r], pi[2 * a + r]
            for c in range(2):
                cr, ci = C[r][c]
                if cr == 0 and ci == 0: continue
                br, bi = pr[2 * b + c], pi[2 * b + c]
                # (C p_b)_r component: (cr + i ci)(br + i bi) = (cr*br - ci*bi) + i (cr*bi + ci*br)
                vr = cr * br - ci * bi; vi = cr * bi + ci * br
                # Re( conj(p_a_r) * v ) = ar*vr + ai*vi
                re_sum += ar * vr + ai * vi
    quad = diag - 2 * re_sum
    return Fraction(quad, norm2), norm2

for lvl in range(2, maxlvl + 1):
    t0 = time.time(); H, n, links = build(lvl)
    if 2 * n <= 2048:
        w, V = np.linalg.eigh(H.toarray()); w, V = w[:4], V[:, :4]
    else:
        w, V = lowest(H)
    psi = V[:, 0]
    res = np.linalg.norm(H @ psi - w[0] * psi) / np.linalg.norm(psi)
    q, norm2 = exact_rayleigh(psi, n, links)
    qf = float(q)
    say(f"level {lvl} dim {2*n:7d}: float lambda_min estimate {w[0]:.7f} (residual {res:.1e});  CERTIFIED exact Rayleigh quotient of rounded vector = "
        f"{qf:.9f}  (= {q.numerator}/{q.denominator}, |p|^2={norm2});  E_bulk <= {qf:.7f}  ({time.time()-t0:.0f}s)")
    # also a certified upper bound for the SECOND Kramers pair would need orthogonality; not attempted.

say("Conclusion: E_bulk <= lambda_min(H^pin_m) <= certified value at every level; the sequence of certified values is non-increasing.")
with open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'results', 'phase5a_certified_upper_bound.txt'), 'w') as f:
    f.write("\n".join(OUT) + "\n")
