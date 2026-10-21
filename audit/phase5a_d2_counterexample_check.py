"""
Phase 5a / D2: independent cross-check of candidate flux-matched periodic decorations with E_per > 8.770 found by
audit/phase5a_d2_census_verify.py.  Two independent checks per candidate:
  (i)  dense Brillouin-zone grid (16^3) + refinement with the D2 Bloch code;
  (ii) explicit real-space supercell torus Hamiltonian H = 24 - A on N^3 copies of the L' cell (sparse, 2*8*N^3 dim),
       built directly from the cube geometry (owner map + unit panels) and the audited clifford_link matrices, lowest
       eigenvalue by scipy eigsh.  Torus spectrum = union of Bloch spectra over the commensurate q's, so
       lambda_min(torus N) >= E_per with equality iff the band minimum is commensurate;  also lambda_min <= E at any
       commensurate q, in particular the 8^3 grid minimum when N is a multiple of 8.
  (iii) holonomy class count on the torus recomputed with 2x2 matrices (clifford_link, q8label) instead of Q8 tables.
Usage: OMP_NUM_THREADS=1 python3 -u -I audit/phase5a_d2_counterexample_check.py  (reads candidates from the list below)
"""
import os, sys, time, itertools, collections
for _v in ('OPENBLAS_NUM_THREADS', 'OMP_NUM_THREADS', 'MKL_NUM_THREADS'): os.environ.setdefault(_v, '1')
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import numpy as np, scipy.sparse as sps, scipy.sparse.linalg as spl
import importlib.util
spec = importlib.util.spec_from_file_location('d2', os.path.join(HERE, 'phase5a_d2_census_verify.py')); d2 = importlib.util.module_from_spec(spec); spec.loader.exec_module(d2)
from independent_clifford_q8_audit import clifford_link, q8label, U3

OUT = os.path.join(HERE, 'results', 'phase5a_d2_counterexample_check.txt')
fh = open(OUT, 'a')
def log(*a):
    s = " ".join(str(x) for x in a); print(s, flush=True); fh.write(s + "\n"); fh.flush()

CANDS = [  # (S rows in L-coords, SO3Z frame indices per coset in D2/B2a coset order)
    ([[1, 0, 6], [0, 1, 6], [0, 0, 8]], [0, 15, 1, 3, 3, 6, 8, 0]),
    ([[1, 0, 5], [0, 1, 6], [0, 0, 8]], [0, 19, 20, 0, 10, 3, 10, 17]),
    ([[1, 3, 1], [0, 4, 0], [0, 0, 2]], [0, 0, 14, 19, 22, 4, 1, 1]),
]
if len(sys.argv) > 1:  # extra candidates "S;frames" e.g. "1,0,6,0,1,6,0,0,8;0,15,1,3,3,6,8,0"
    for arg in sys.argv[1:]:
        s, f = arg.split(';'); s = [int(x) for x in s.split(',')]; CANDS.append(([s[0:3], s[3:6], s[6:9]], [int(x) for x in f.split(',')]))

def torus_H(cr, frames, N):
    """Real-space pinned operator on the torus Z^3 / (N L'): chairs = cosets x (Z/N)^3 supercell index."""
    S = cr.S; k = cr.k; Bp = cr.Bp.astype(float); BpinvT = np.linalg.inv(Bp.T)
    def chair_id(x):            # ambient lattice point -> (coset, alpha mod N)
        m = d2.to_L(x); c = cr.coset(m); r = cr.reps[c]
        al = BpinvT @ (np.asarray(x) - d2.from_L(r)).astype(float)   # (x - x_rep) in L'-coordinates
        ali = np.rint(al).astype(int); assert np.allclose(al, ali)
        return c, tuple(ali % N)
    idx = {}
    for c in range(k):
        for al in itertools.product(range(N), repeat=3): idx[(c, al)] = len(idx)
    n = len(idx); assert n == k * N ** 3
    rows, cols, vals = [], [], []
    npan = 0
    for c, m in enumerate(cr.reps):
        for al in itertools.product(range(N), repeat=3):
            x = d2.from_L(m) + np.rint(np.array(al) @ Bp).astype(int)
            a = idx[(c, al)]
            for (dd, nn, u) in d2.PANELS:
                y = x + dd; c2, al2 = chair_id(y); b = idx[(c2, al2)]
                C = clifford_link(d2.SO3Z[frames[c]], d2.SO3Z[frames[c2]], nn)
                for s in range(2):
                    for t in range(2):
                        rows.append(2 * a + s); cols.append(2 * b + t); vals.append(-C[s, t])
                npan += 1
    A = sps.csr_matrix((vals, (rows, cols)), shape=(2 * n, 2 * n))
    H = 24.0 * sps.identity(2 * n, format='csr') + A
    herm = abs(H - H.getH()).max()
    return H, herm, npan

def torus_flux_matrices(cr, frames):
    cls = collections.Counter(); internal = 0
    for m in cr.reps:
        x = d2.from_L(m)
        for u in U3:
            c = x + np.array(u)
            for (i, j) in ((0, 1), (1, 2), (0, 2)):
                ei = d2.I3[i]; ej = d2.I3[j]; ring = [c, c + ei, c + ei + ej, c + ej]
                own = [d2.owner(cc) for cc in ring]
                if len({tuple(o) for o in own}) == 1: internal += 1; continue
                W = np.eye(2, dtype=complex)
                for t in range(4):
                    oa, ob = own[t], own[(t + 1) % 4]
                    if (oa == ob).all(): continue
                    Ma = d2.SO3Z[frames[cr.coset(d2.to_L(oa))]]; Mb = d2.SO3Z[frames[cr.coset(d2.to_L(ob))]]
                    W = W @ clifford_link(Ma, Mb, ring[(t + 1) % 4] - ring[t])
                cls[q8label(W)] += 1
    inter = sum(cls.values()); tr = sum(v for kk, v in cls.items() if kk not in ('+1', '-1'))
    return internal, inter, dict(cls), (1 - cls['+1'] / inter, tr / inter, cls['-1'] / inter)

log("#" * 100); log(f"# phase5a_d2_counterexample_check.py  cmd: OMP_NUM_THREADS=1 python3 -u -I audit/phase5a_d2_counterexample_check.py {' '.join(sys.argv[1:])}")
for S, frames in CANDS:
    t0 = time.time(); cr = d2.crystal(np.array(S)); fr = np.array(frames)
    log("=" * 100); log(f"candidate S={S} frames={frames} (k={cr.k}); frames as matrices: {[d2.SO3Z[g].tolist() for g in frames]}")
    r8 = cr.band_bottom(fr, ngrid=8); r16 = cr.band_bottom(fr, ngrid=16, nstart=5)
    log(f" (i) Bloch: 8^3 grid min={r8['grid_min']:.9f} refined={r8['E']:.9f} theta={np.round(r8['theta'],5).tolist()};  16^3 grid min={r16['grid_min']:.9f} refined={r16['E']:.9f} theta={np.round(r16['theta'],5).tolist()}; |diff|={abs(r8['E']-r16['E']):.2e}")
    # gap check at the minimum and generic q
    E = cr.bloch_blocks(fr); w = np.linalg.eigvalsh(cr.Hq(E, r16['q']))
    log(f"     eigenvalues at the minimum: {np.round(w[:4],6).tolist()}; max eigenvalue over 16^3 grid: {np.linalg.eigvalsh(cr.Hq_batch(E, (2*np.pi*np.linalg.solve(cr.Bp.astype(float), np.array(list(itertools.product(np.arange(16)/16, repeat=3))).T)).T)).max():.4f} (<=48)")
    fn, ft, fm = cr.flux_fractions(fr)
    internal, inter, cls, (fn2, ft2, fm2) = torus_flux_matrices(cr, fr)
    log(f" (iii) flux via Q8 tables: nontriv={fn:.6f} traceless={ft:.6f} -1={fm:.6f};  via 2x2 matrices+q8label: internal={internal} inter={inter} classes={cls} -> nontriv={fn2:.6f} traceless={ft2:.6f} -1={fm2:.6f}; agree: {np.allclose([fn,ft,fm],[fn2,ft2,fm2])}; "
        f"flux-matched (0.03,0.04,0.04): {d2.flux_matched(fn2, ft2, fm2)}; FR30 fractions {17/36:.4f} {55/144:.4f} {13/144:.4f}")
    for N in (4, 8):
        t = time.time(); H, herm, npan = torus_H(cr, fr, N)
        lam = spl.eigsh(H, k=2, which='SA', tol=1e-10, maxiter=20000)[0]
        # the lowest torus eigenvalue must equal the min over the commensurate Bloch points theta in (1/N)Z^3
        th = np.array(list(itertools.product(np.arange(N) / N, repeat=3)))
        Q = (2 * np.pi * np.linalg.solve(cr.Bp.astype(float), th.T)).T
        comm = np.linalg.eigvalsh(cr.Hq_batch(E, Q))[:, 0].min()
        log(f" (ii) real-space torus N={N}: dim={H.shape[0]}, panels={npan} (=24*8*N^3: {npan==24*8*N**3}), hermiticity defect={herm:.1e}, lambda_min={lam.min():.9f} "
            f"(Bloch min over commensurate grid {comm:.9f}, |diff|={abs(lam.min()-comm):.1e});  lambda_min >= E_per(refined): {lam.min() >= r16['E'] - 1e-9}  [{time.time()-t:.1f}s]")
    log(f" VERDICT: E_per = {r16['E']:.6f} {'>' if r16['E'] > 8.770 else '<='} 8.770 with flux-matched={d2.flux_matched(fn2, ft2, fm2)}   [{time.time()-t0:.1f}s]")
log(f"[done]")
