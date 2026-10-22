"""
Phase 5B / Workstream E, task E1: level-6 pinned ground state and an EXACT rational upper bound for E_bulk.

  E_bulk <= lambda_min(H^pin_6) <= <p, (24 I - A) p> / <p, p>      for ANY nonzero vector p   (compression theorem,
  PHASE5A_INFINITE_VOLUME_FRAMEWORK.md Thm 3.2 + Rayleigh).

Steps
  1. geometry of T_6 (262144 chairs, 128^3 owner grid) and H = 24 I - A, built with the vectorised grid code of
     audit/phase5a_level6_structure.py (validated there entry by entry against the object builders at levels <= 5;
     re-validated here at level 4 before the level-6 run);
  2. LOBPCG (block 4, diagonal preconditioner, seed 0) for the lowest Kramers pair, in chunks with warm restart, until
     the residual ||H psi - lambda psi|| of the ground vector is <= 1e-6 (or the wall-clock budget is exhausted: the
     Rayleigh-quotient bound stays rigorous either way, only its tightness depends on convergence);
  3. p = round(2^SCALE_BITS * psi) as a Gaussian-integer vector; <p, H p> and <p, p> computed EXACTLY in integer
     arithmetic THREE independent ways:
       (A) numpy int64 per-panel products grouped by Q8 label, chunk sums accumulated in Python integers (overflow-safe
           by the explicit bound stated in the code);
       (B) pure-Python loop over the panel list in a different order (sorted by tile), with the Q8 matrices taken from
           the Gaussian-integer link table, accumulated per tile and then summed;
       (C) float sanity check with the scipy sparse operator (not part of the certificate).
     (A) and (B) must agree bit for bit; the certified bound is the Fraction they return.
Outputs: audit/results/phase5b_e_fr30_level6_groundstate.npy (complex128, length 524288, unit norm; column order =
         depth-first tile order of tiles_at_level, 2 spinor components per tile),
         audit/results/phase5b_e_level6_certificate.txt.
Run from the repository root:  OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 python3 -u -I audit/phase5b_e_level6_certificate.py [level=6] [budget_s=3300]
"""
import os, sys, time, resource, warnings, datetime
from fractions import Fraction
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
RES = os.path.join(HERE, 'results')
import numpy as np, scipy.sparse as sps, scipy.sparse.linalg as spl
import phase5a_level6_structure as l6          # geometry + H builder (import has no side effects: main is guarded)
from phase5a_level6_structure import Q8_NAMES, Q8_MATS

LEVEL = int(sys.argv[1]) if len(sys.argv) > 1 else 6
BUDGET = float(sys.argv[2]) if len(sys.argv) > 2 else 3300.0
TOL = 1e-6; BLOCK = 4; CHUNK = 600; MAXITER = 6000; SEED = 0
SCALE_BITS = 26
VEC = os.path.join(RES, f'phase5b_e_fr30_level{LEVEL}_groundstate.npy')
CERT = os.path.join(RES, f'phase5b_e_level{LEVEL}_certificate.txt')
T_START = time.time()
OUT = []
def say(s=''):
    print(s, flush=True); OUT.append(s)
    with open(CERT, 'w') as f: f.write("\n".join(OUT) + "\n")
def rss(): return resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 1e6

say(f"PHASE 5B-E / E1: level-{LEVEL} pinned FR30 Clifford operator, exact Rayleigh-quotient certificate   (started {datetime.datetime.now():%Y-%m-%d %H:%M:%S}, OMP_NUM_THREADS={os.environ.get('OMP_NUM_THREADS')})")
# ---------------------------------------------------------------- 1. geometry and H
if LEVEL >= 5:
    t0 = time.time(); geo4 = l6.build_geometry('fr30', 4, say); H4 = l6.build_H(geo4, 24.0)
    l6.validate_against_objects('fr30', 4, geo4, H4, 24.0, say); del geo4, H4
geo = l6.build_geometry('fr30', LEVEL, say)
n = geo['n']; N = 2 * n
t0 = time.time(); H = l6.build_H(geo, 24.0)
herm = float(abs((H - H.getH()).data).max()) if (H - H.getH()).nnz else 0.0
say(f"   H = 24 I - A: dim {N}, nnz {H.nnz}, max|H - H^dagger| = {herm:.1e}  ({time.time()-t0:.1f}s, rss {rss():.2f} GB)")
assert herm == 0.0

# ---------------------------------------------------------------- 2. LOBPCG
rng = np.random.default_rng(SEED)
X = rng.standard_normal((N, BLOCK)) + 1j * rng.standard_normal((N, BLOCK))
dinv = 1.0 / H.diagonal().real
Mpre = spl.LinearOperator(H.shape, matvec=lambda v: dinv * v, matmat=lambda B: dinv[:, None] * B, dtype=complex)
it_total = 0; sec_per_it = None; converged = False
while True:
    left = BUDGET - (time.time() - T_START)
    it_this = min(CHUNK, MAXITER - it_total)
    if it_this <= 0: say("   maxiter reached"); break
    if sec_per_it is not None:
        afford = int((left - 120.0) / sec_per_it)
        if afford < 10: say(f"   wall-clock budget {BUDGET:.0f}s exhausted (residual not yet below tol)"); break
        it_this = min(it_this, afford)
    tc = time.time()
    with warnings.catch_warnings():
        warnings.simplefilter('ignore')
        w, V, hist = spl.lobpcg(H, X, M=Mpre, largest=False, tol=TOL, maxiter=it_this, retResidualNormsHistory=True)
    n_it = len(hist); it_total += n_it; dt = time.time() - tc; sec_per_it = dt / max(n_it, 1)
    lam, V, res = l6.ritz(H, V); X = V
    say(f"   lobpcg chunk: {n_it:4d} it ({dt:.0f}s, {sec_per_it:.2f}s/it), cumulative {it_total:5d}: lambda={np.array2string(lam, precision=8, max_line_width=200)} "
        f"res={np.array2string(res, max_line_width=200, formatter={'float_kind': lambda x: f'{x:.1e}'})}  rss {rss():.2f} GB")
    if res[0] <= TOL and res[1] <= TOL: converged = True; say(f"   converged: ground Kramers pair residuals <= {TOL:g}"); break
    if n_it < it_this and n_it <= 3: say("   lobpcg stalls; stopping"); break
psi = V[:, 0] / np.linalg.norm(V[:, 0])
lam0 = float(np.real(np.vdot(psi, H @ psi))); res0 = float(np.linalg.norm(H @ psi - lam0 * psi))
say(f" ground vector: Rayleigh quotient {lam0:.10f}, residual {res0:.2e}, Kramers partner {lam[1]:.10f} (split {abs(lam[1]-lam[0]):.1e}), next pair {lam[2]:.8f} (gap {lam[2]-lam[0]:.3e}); iterations {it_total}, converged={converged}  ({time.time()-T_START:.0f}s)")
np.save(VEC, psi.astype(np.complex128))
say(f" saved {os.path.relpath(VEC, os.path.dirname(HERE))}  (complex128, {psi.nbytes/1e6:.1f} MB)")

# ---------------------------------------------------------------- 3. exact certificate
t0 = time.time()
S = 1 << SCALE_BITS
pr = np.rint(psi.real * S).astype(np.int64); pi_ = np.rint(psi.imag * S).astype(np.int64)
pmax = int(max(np.abs(pr).max(), np.abs(pi_).max()))
say(f" rounded vector p = round(2^{SCALE_BITS} psi): max |entry| = {pmax} (< 2^{pmax.bit_length()}), nonzero entries {int(((pr != 0) | (pi_ != 0)).sum())} of {N}")
# overflow bound for method (A): each per-row term |ar*vr + ai*vi| <= 2 pmax^2; a panel has 2 rows -> <= 4 pmax^2;
# a chunk of CH panels sums to <= 4 CH pmax^2, which must stay below 2^62.
CH = 1 << 14
assert 4 * CH * pmax * pmax < (1 << 62), "chunk bound violated"
assert 2 * CH * pmax * pmax < (1 << 62)
def chunked_int_sum(arr):
    tot = 0
    for s in range(0, len(arr), CH): tot += int(arr[s:s+CH].sum())
    return tot
norm2_A = chunked_int_sum(pr * pr + pi_ * pi_)       # entries <= 2 pmax^2 each
ea, eb, lab = geo['ea'], geo['eb'], geo['lab']
# Gaussian-integer table of the Q8 matrices (exact), consistent with Q8_MATS
GI = {}
for name in Q8_NAMES:
    C = Q8_MATS[name]
    GI[name] = [[(int(np.rint(C[r, c].real)), int(np.rint(C[r, c].imag))) for c in range(2)] for r in range(2)]
    assert np.allclose(np.array([[complex(*GI[name][r][c]) for c in range(2)] for r in range(2)]), C)
re_sum_A = 0
for li, name in enumerate(Q8_NAMES):
    sel = np.nonzero(lab == li)[0]
    if len(sel) == 0: continue
    a = ea[sel]; b = eb[sel]; acc = np.zeros(len(sel), dtype=np.int64)
    for r in range(2):
        ar = pr[2*a + r]; ai = pi_[2*a + r]
        for c in range(2):
            cr, ci = GI[name][r][c]
            if cr == 0 and ci == 0: continue
            br = pr[2*b + c]; bi = pi_[2*b + c]
            vr = cr * br - ci * bi; vi = cr * bi + ci * br           # (C p_b)_r = (cr + i ci)(br + i bi)
            acc += ar * vr + ai * vi                                 # Re( conj(p_a,r) * v )
    re_sum_A += chunked_int_sum(acc)
quad_A = 24 * norm2_A - 2 * re_sum_A
q_A = Fraction(quad_A, norm2_A)
say(f" (A) numpy-int64/chunked Python-int evaluation: <p,p> = {norm2_A}, Re sum_f <p_a, C_f p_b> = {re_sum_A}, <p,Hp> = {quad_A}  ({time.time()-t0:.0f}s)")

# (B) pure Python, different order: panels sorted by (a, b), accumulated per tile a
t0 = time.time()
order = np.lexsort((eb, ea)); ea_s = ea[order].tolist(); eb_s = eb[order].tolist(); lab_s = lab[order].tolist()
prl = pr.tolist(); pil = pi_.tolist()
GIL = [GI[name] for name in Q8_NAMES]
per_tile = [0] * n
for a, b, l in zip(ea_s, eb_s, lab_s):
    C = GIL[l]; acc = 0
    for r in range(2):
        ar = prl[2*a + r]; ai = pil[2*a + r]; row = C[r]
        for c in range(2):
            cr, ci = row[c]
            if cr == 0 and ci == 0: continue
            br = prl[2*b + c]; bi = pil[2*b + c]
            acc += ar * (cr * br - ci * bi) + ai * (cr * bi + ci * br)
    per_tile[a] += acc
re_sum_B = sum(per_tile)
norm2_B = 0
for a in range(n):
    for r in range(2): norm2_B += prl[2*a + r] ** 2 + pil[2*a + r] ** 2
quad_B = 24 * norm2_B - 2 * re_sum_B
q_B = Fraction(quad_B, norm2_B)
say(f" (B) pure-Python per-tile evaluation:          <p,p> = {norm2_B}, Re sum_f <p_a, C_f p_b> = {re_sum_B}, <p,Hp> = {quad_B}  ({time.time()-t0:.0f}s)")
agree = (q_A == q_B) and (norm2_A == norm2_B) and (quad_A == quad_B)
say(f" (A) == (B) bit for bit: {agree}")
# (C) float sanity
pc = (pr + 1j * pi_).astype(complex)
q_C = float(np.real(np.vdot(pc, H @ pc)) / np.real(np.vdot(pc, pc)))
say(f" (C) scipy float Rayleigh quotient of the same integer vector: {q_C:.12f}  (|C - A| = {abs(q_C - float(q_A)):.1e}, sanity only)")
assert agree
qf = float(q_A)
say("")
say("=" * 100)
say(f" CERTIFIED (exact integer arithmetic, two independent evaluations agree):")
say(f"   E_bulk <= lambda_min(H^pin_{LEVEL}) <= {q_A.numerator}/{q_A.denominator}")
say(f"   = {qf:.12f}   (decimal; all digits shown are exact to the displayed precision)")
say(f"   float LOBPCG value {lam0:.10f}, difference certificate - float = {qf - lam0:.2e}; residual of float vector {res0:.1e}")
say(f"   previous certified bound (level 5): 2476138622922986/281474983842677 = 8.797011333;  improvement {8.797011333 - qf:.6f}")
say(f" total wall time {time.time()-T_START:.0f}s, max rss {rss():.2f} GB")
say("=" * 100)
