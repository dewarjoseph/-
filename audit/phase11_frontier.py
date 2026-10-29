#!/usr/bin/env python3
"""Phase XI, Part II: the certified extremal frontier.

Rule of elimination (frozen in audit/results/phase11_preregistration.json before any value below was computed):
  a decoration r is PROVEN INFERIOR to class 1387 when a rigorous upper bound U(r) on E_*(r) satisfies U(r) < L_ref, where L_ref
  is a rational lower bound on E_*(1387) carried by an independently verified certificate.  Upper bounds are exact rational
  Rayleigh quotients of integer vectors on pinned supertiles T_L(r) (L = 3, 4, 5): T_L(r) is a legal patch, the pinned operator is
  the compression of the hull operator, so lambda_min(T_L) >= E_*(r) := inf over legal patches (= the hull floor when the hull is
  minimal; for every r the frame substitution is irreducible -- Cayley digraph of the generated group -- and the hull is a finite
  union of minimal components permuted by global rigid motions that preserve the links, so E_* is the same on all of them).
  No prediction, screening score or extrapolation is used to eliminate anything.
Stages (extended space, one decoration per S3-orbit; Y_L is constant on S3-orbits because conjugating the decoration by an axis
permutation Q rotates every supertile rigidly, and rigid rotations preserve the Pauli links):
  X3  exact Y3 upper bound for all 280 332 orbit representatives
  X4  exact Y4 upper bound for the survivors of X3
  X5  exact Y5 upper bound for the survivors of X4
Independent of the Phase X code (uses phase11_chair only).
Usage: python -u -I audit/phase11_frontier.py <stage> [nproc]   (stages: reps, X3, X4, X5, census) -> audit/results/phase11_frontier_*.jsonl"""
import os, sys, json, time, math, itertools, types
from fractions import Fraction
sys.modules.setdefault('resource', types.SimpleNamespace(getrusage=lambda *a: types.SimpleNamespace(ru_maxrss=0), RUSAGE_SELF=0))
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); RES = os.path.join(HERE, 'results')
import numpy as np, scipy.sparse as sps, scipy.sparse.linalg as sla
import phase11_chair as C
T0 = time.time()
def log(*a): print(f"[{time.time()-T0:7.0f}s]", *a, flush=True)
N8 = 6 ** 8
L_REF = Fraction(87999987, 10 ** 7)       # <= 8.7999987798, the certified Lambda_15(1387) (rounded down; see preregistration)

# ------------------------------------------------------------------ S3 orbits on the extended space
def conj_decoration(dec, Q):
    """decoration of the tiling rotated by the axis permutation matrix Q: child of octant v moves to octant Qv and its permutation
    matrix P becomes Q P Q^T (the sign pattern D_{1-2v} is carried along: Q D_{1-2v} Q^T = D_{1-2Qv})"""
    Qm = C.perm_matrix(Q); out = [None] * 8
    def conj(p):
        M = Qm @ C.perm_matrix(p) @ Qm.T; return tuple(int(np.argmax(M[i])) for i in range(3))
    out[0] = conj(dec[0])
    for k, v in enumerate(C.U3):
        w = tuple(int(x) for x in Qm @ np.array(v)); out[1 + C.U3.index(w)] = conj(dec[k + 1])
    return tuple(out)
def ext_index(dec): return sum(C.PERMS.index(p) * 6 ** c for c, p in enumerate(dec))
def orbit_reps():
    seen = np.zeros(N8, bool); reps = []
    for j in range(N8):
        if seen[j]: continue
        d = C.extended_decoration(j); orb = {ext_index(conj_decoration(d, Q)) for Q in C.PERMS}
        for i in orb: seen[i] = True
        reps.append(min(orb))
    return reps

# ------------------------------------------------------------------ supertile operators in a fixed tile order
class Level:
    """T_L for any decoration, with tiles ordered by centroid (the set of chairs of T_L does not depend on the decoration)"""
    def __init__(self, L):
        self.L = L; G, T = C.supertile(C.extended_decoration(0), L); X = C.centroid14(G, T); self.K = 14 * 2 ** (L + 3)
        o = np.argsort(self.key(X)); G, T = G[o], T[o]; self.keys = self.key(C.centroid14(G, T)); self.n = len(G)
        P = C.Patch(G, T); self.a, self.b, self.k = P.panels(); self.T = T
    def key(self, X): return (X[:, 0] * self.K + X[:, 1]) * self.K + X[:, 2]
    def frames(self, dec):
        G, T = C.supertile(dec, self.L); X = C.centroid14(G, T); o = np.argsort(self.key(X))
        assert np.array_equal(self.key(X)[o], self.keys), 'geometry differs'
        return G[o]
    def H(self, dec):
        G = self.frames(dec); U = C.link_matrices(G, self.a, self.b, self.k); return C.hermitian(self.n, self.a, self.b, U, 24)

def exact_upper(H, v):
    """exact Rayleigh quotient (num, den) of the integer rounding of v (H with Gaussian-integer entries)"""
    v = v / np.abs(v).max(); s = 2 ** 20
    xr = np.rint(v.real * s).astype(np.int64); xi = np.rint(v.imag * s).astype(np.int64)
    Hr = H.real.tocsr(); Hi = H.imag.tocsr()
    assert np.array_equal(Hr.data, np.rint(Hr.data)) and np.array_equal(Hi.data, np.rint(Hi.data))
    Hr = Hr.astype(np.int64); Hi = Hi.astype(np.int64)
    yr = Hr @ xr - Hi @ xi; yi = Hr @ xi + Hi @ xr                       # |entries| <= 48 * 2^20: no int64 overflow
    num = int(np.sum((xr * yr).astype(object))) + int(np.sum((xi * yi).astype(object)))
    den = int(np.sum((xr * xr).astype(object))) + int(np.sum((xi * xi).astype(object)))
    return num, den

def lowest(H, tol=1e-10):
    n = H.shape[0]
    if n <= 512:
        w, V = np.linalg.eigh(H.toarray()); return float(w[0]), V[:, 0]
    w, V = sla.eigsh(H, k=1, which='SA', tol=tol, ncv=min(n - 1, 40)); return float(w[0]), V[:, 0]

_LV = {}
def upper_job(args):
    j, L = args
    if L not in _LV: _LV[L] = Level(L)
    H = _LV[L].H(C.extended_decoration(j)); lam, v = lowest(H); num, den = exact_upper(H, v)
    return j, lam, num, den

def run_stage(name, L, js, nproc):
    import multiprocessing as mp
    out = os.path.join(RES, f'phase11_frontier_{name}.jsonl'); done = set()
    if os.path.exists(out):
        for l in open(out): done.add(json.loads(l)['j'])
    todo = [j for j in js if j not in done]; log(f'{name}: {len(js)} decorations, {len(done)} done, {len(todo)} to do')
    t0 = time.time()
    with mp.Pool(nproc) as pool, open(out, 'a') as f:
        for i, (j, lam, num, den) in enumerate(pool.imap_unordered(upper_job, [(j, L) for j in todo], chunksize=16)):
            inferior = num * L_REF.denominator < L_REF.numerator * den
            f.write(json.dumps({'j': j, 'L': L, 'float': lam, 'upper_num': str(num), 'upper_den': str(den), 'upper': num / den, 'inferior': inferior}) + '\n')
            if i % 5000 == 0: f.flush(); log(f'{name}: {i + 1}/{len(todo)} [{time.time()-t0:.0f}s]')
    return load_stage(name)
def load_stage(name):
    """rows of a stage, from the .jsonl file or (as committed for X3, 280 332 rows) its gzip"""
    p = os.path.join(RES, f'phase11_frontier_{name}.jsonl')
    if not os.path.exists(p) and os.path.exists(p + '.gz'):
        import gzip
        return {r['j']: r for r in (json.loads(l) for l in gzip.open(p + '.gz', 'rt'))}
    return {r['j']: r for r in (json.loads(l) for l in open(p))}

def census_job(cls):
    """independent census bracket of one gauge class (representative cls): certified free level-3 lower bound (Theorem X.2, banded
    Higham certificate) and exact level-4 pinned upper bound"""
    dec = C.proper_decoration(cls); G, T = C.supertile(dec, 3); Hf = C.operators(G, T, free=True)
    f = float(np.linalg.eigvalsh(Hf.toarray())[0]); mu = Fraction(math.floor((f - 1e-7) * 2 ** 20), 2 ** 20); low, _ = C.banded_cert(Hf, mu)
    if '4' not in _LV: _LV['4'] = Level(4)
    H = _LV['4'].H(C.extended_decoration(ext_index(dec))); lam, v = lowest(H); num, den = exact_upper(H, v)
    return {'class': cls, 'F3_float': f, 'F3_certified': low, 'Y4_float': lam, 'Y4_num': str(num), 'Y4_den': str(den), 'Y4_upper': num / den}

if __name__ == '__main__':
    os.environ.setdefault('OMP_NUM_THREADS', '1')
    if sys.argv[1] == 'census':
        import multiprocessing as mp
        cen = json.load(open(os.path.join(RES, 'phase10_census.json')))['classes']; nproc = int(sys.argv[2]) if len(sys.argv) > 2 else 4
        with mp.Pool(nproc) as pool: rows = pool.map(census_job, [r['class'] for r in cen], chunksize=8)
        json.dump({'rows': rows}, open(os.path.join(RES, 'phase11_frontier_census.json'), 'w'), indent=0)
        fr = next(r for r in rows if r['class'] == 1386)
        log('census:', len(rows), 'min certified F3', min(r['F3_certified'] for r in rows), 'FR30 class', fr); sys.exit()
    stage = sys.argv[1]; nproc = int(sys.argv[2]) if len(sys.argv) > 2 and sys.argv[2].isdigit() else 4
    if stage == 'reps':
        reps = orbit_reps(); json.dump({'orbit_representatives': reps}, open(os.path.join(RES, 'phase11_frontier_reps.json'), 'w')); log(len(reps), 'orbit representatives')
    elif stage in ('X3', 'X4', 'X5'):
        L = int(stage[1]); reps = json.load(open(os.path.join(RES, 'phase11_frontier_reps.json')))['orbit_representatives']
        if L == 3: js = reps
        else:
            prev = load_stage(f'X{L - 1}'); js = sorted(j for j in reps if j in prev and not prev[j]['inferior'])
        res = run_stage(stage, L, js, nproc); surv = [j for j in js if not res[j]['inferior']]
        log(f'{stage}: {len(js)} evaluated, {len(js) - len(surv)} proven inferior, {len(surv)} survive')
    elif stage == 'list':
        # python phase11_frontier.py list <name> <L> <nproc>: Y_L exact upper bounds for a preregistered rule list
        name, L, nproc = sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
        pre = json.load(open(os.path.join(RES, 'phase11_preregistration.json')))
        S = C.perm_matrix((1, 0, 2))
        def twin(d): return tuple(tuple(int(np.argmax((C.perm_matrix(p) @ S)[i])) for i in range(3)) for p in d)
        if name == 'twins':
            js = []
            for r in pre['part_II_twin_criterion']['classes']:
                d = C.proper_decoration(r); js += [ext_index(d), ext_index(twin(d))]
        elif name == 'counterfactual':
            cf = pre['part_V_counterfactuals']; js = [ext_index(C.proper_decoration(4752)), ext_index(C.proper_decoration(4753))] + cf['neighbours_FR30'] + cf['neighbours_4753']
        else: raise ValueError(name)
        run_stage(f'{name}_Y{L}', L, list(dict.fromkeys(js)), nproc)
