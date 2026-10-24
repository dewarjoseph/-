#!/usr/bin/env python3
"""Phase X, Part III stage C: the controlled extension to IMPROPER frames.

Configuration space: a decoration assigns to each of the 8 children any of the 6 permutations (not only the 3 of the parity
that makes the frame proper): 6^8 = 1,679,616 decorations, encoded j = sum_c d_c 6^c (c = 0 centre, c = 1..7 octants
U3[c-1], d_c indexing itertools.permutations(range(3))).  Every permutation maps the chair to itself, so the GEOMETRY is that
of Chair44 (identical chairs and panels); frames may now have det = -1.  Links: the same Pauli formula, still in Q8 (M^T n is
still a signed unit vector).  Operator: the same pinned 24 - A_U.  Gauge action, geometry and normalisation are unchanged;
only the admissibility condition (det = +1) is dropped.  Proper decorations form a subset (the Phase V-B census).
Screening funnel (calibrated on the proper census, where every Y2, Y3, Y4 is known, and fixed before any extended-space value
was computed; an earlier draft screening on the top 1.8% by Y2 was discarded because that set recalls only 5% of the census's
top-20 classes by Y4):
  stage 1  Y2 for all 6^8 decorations (batched; tiles matched to a reference ordering by their integer centroids)
  stage 2  S3-orbit representatives with Y2 in the top 50% (proper-census recall of the top-10/20/50 classes by Y4: 1.00)
  stage 3  Y3 (sparse Lanczos) for those representatives
  stage 4  Y4 for the top 10% by Y3 (proper-census recall of the top-20 by Y4: 1.00); Y5 for the 10 best distinct by Y4
Also (Theorem X.3 in the extended space): f1 computes the free level-1 bottom F1 of all 6^8 decorations, and F2, F3 for those whose
level-1 supertile is flat (F1 = 0).
Usage: python -u -I audit/phase10_improper.py y2 [nproc] | y3 [nproc] | y45 [nproc] | f1 [nproc] | pack [nproc] | certify <j>"""
import os, sys, json, time, math, types, itertools
sys.modules.setdefault('resource', types.SimpleNamespace(getrusage=lambda *a: types.SimpleNamespace(ru_maxrss=0), RUSAGE_SELF=0))
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); RES = os.path.join(HERE, 'results')
import numpy as np, scipy.sparse.linalg as sla
import phase9_pair as P9
T0 = time.time()
def log(*a): print(f"[{time.time()-T0:7.0f}s]", *a, flush=True)
PERMS = list(itertools.permutations(range(3))); N8 = 6 ** 8

def dec_of(j):
    d = [(j // 6 ** c) % 6 for c in range(8)]; dec = {'0': PERMS[d[0]]}
    for c, v in enumerate(P9.U3): dec[v] = PERMS[d[c + 1]]
    return dec
def is_proper(j):
    d = [(j // 6 ** c) % 6 for c in range(8)]
    return P9.psign(PERMS[d[0]]) == 1 and all(P9.psign(PERMS[d[c + 1]]) == (1 if sum(v) % 2 == 0 else -1) for c, v in enumerate(P9.U3))
def census_index(j):
    """the Phase V-B census index of a proper decoration"""
    return P9.index_of(dec_of(j))
def proper_mask():
    """boolean array over all 6^8 decorations: det = +1 for every child frame"""
    D = np.array([(np.arange(N8) // 6 ** c) % 6 for c in range(8)]); sgn = np.array([P9.psign(p) for p in PERMS])
    par = np.array([1] + [1 if sum(v) % 2 == 0 else -1 for v in P9.U3]); return (sgn[D] == par[:, None]).all(0)

class Batched:
    """pinned level-L operators for many decorations at once (all share the chair geometry)"""
    def __init__(self, L):
        self.L = L; ref = P9.build([P9.decoration(0)] * L); self.n = ref['n']; self.a, self.b, self.ax = ref['a'], ref['b'], ref['ax']
        X = 14 * ref['T'] + 13 * ref['G'].sum(-1); self.K = 14 * 2 ** (L + 2); keys = self.key(X); order = np.argsort(keys)
        self.sorted_keys, self.sorted_idx = keys[order], order
        ops = [[(np.diag([1 - 2 * x for x in v]) if c else np.eye(3, dtype=np.int64)) @ P9.pmat(p) for p in PERMS] for c, v in enumerate([(0, 0, 0)] + list(P9.U3))]
        self.ops = np.array(ops)                                                  # (8 children, 6 perms, 3, 3)
        self.trans = np.array([np.array([1, 1, 1])] + [4 * np.array(v) for v in P9.U3])
    def key(self, X): return (X[..., 0] * self.K + X[..., 1]) * self.K + X[..., 2]
    def frames(self, js):
        D = np.array([[(j // 6 ** c) % 6 for c in range(8)] for j in js])          # (B, 8)
        G = np.tile(np.eye(3, dtype=np.int64), (len(js), 1, 1, 1)); T = np.zeros((len(js), 1, 3), np.int64)
        for _ in range(self.L):
            g = self.ops[np.arange(8)[None, :], D]                                # (B, 8, 3, 3)
            T = (2 * T[:, :, None, :] + np.einsum('bnij,cj->bnci', G, self.trans)).reshape(len(js), -1, 3)
            G = np.einsum('bnij,bcjk->bncik', G, g).reshape(len(js), -1, 3, 3)
        X = 14 * T + 13 * G.sum(-1); pos = np.searchsorted(self.sorted_keys, self.key(X)); idx = self.sorted_idx[pos]
        assert (self.sorted_keys[pos] == self.key(X)).all()
        out = np.empty_like(G); np.put_along_axis(out, idx[:, :, None, None], G, axis=1); return out
    def bottoms(self, js, free=False):
        """pinned bottoms Y_L (free: the Neumann bottoms F_L, diagonal = degree inside the supertile)"""
        G = self.frames(js); a, b, ax = self.a, self.b, self.ax; B = len(js)
        ra = G[:, a, ax, :]; rb = G[:, b, ax, :]                                  # rows ax of the frames: signed unit vectors
        ka, kb = np.abs(ra).argmax(-1), np.abs(rb).argmax(-1); sa = np.take_along_axis(ra, ka[..., None], -1)[..., 0]; sb = np.take_along_axis(rb, kb[..., None], -1)[..., 0]
        U = (sa * sb)[..., None, None] * np.einsum('bpij,bpjk->bpik', P9.SIG[ka], P9.SIG[kb])
        diag = np.repeat(np.bincount(a, minlength=self.n) + np.bincount(b, minlength=self.n), 2) if free else 24
        H = np.zeros((B, 2 * self.n, 2 * self.n), complex); H[:, np.arange(2 * self.n), np.arange(2 * self.n)] = diag
        for i in range(2):
            for k in range(2):
                np.add.at(H, (slice(None), 2 * a + i, 2 * b + k), -U[:, :, i, k]); np.add.at(H, (slice(None), 2 * b + k, 2 * a + i), -np.conj(U[:, :, i, k]))
        return np.linalg.eigvalsh(H)[:, 0]

def y2_job(start):
    bt = Batched(2); js = np.arange(start, min(start + 500, N8)); return start, bt.bottoms(js).astype(np.float64)

def f1_job(start):
    bt = Batched(1); js = np.arange(start, min(start + 20000, N8)); return start, bt.bottoms(js, free=True).astype(np.float64)

def cmd_f1(nproc=12):
    """F1 (free level-1 bottom) for all 6^8 decorations: which have a flat level-1 supertile (Theorem X.3); for those, F2 and F3"""
    import multiprocessing as mp
    F1 = np.full(N8, np.nan)
    with mp.Pool(nproc) as pool:
        for s, v in pool.imap_unordered(f1_job, range(0, N8, 20000)): F1[s:s + len(v)] = v
    proper = proper_mask(); flat1 = np.nonzero(F1 < 1e-9)[0]
    out = {'F1_min_proper': float(F1[proper].min()), 'F1_min_improper': float(F1[~proper].min()), 'n_flat_T1': int(len(flat1)), 'n_flat_T1_proper': int(proper[flat1].sum())}
    deeper = {}
    for L in (2, 3):
        bt = Batched(L); cand = flat1 if L == 2 else np.array([j for j in flat1 if deeper[int(j)]['F2'] < 1e-9], int)
        vals = np.concatenate([bt.bottoms(cand[i:i + 500], free=True) for i in range(0, len(cand), 500)]) if len(cand) else np.zeros(0)
        for j, v in zip(cand, vals): deeper.setdefault(int(j), {})[f'F{L}'] = float(v)
    out['n_flat_T2'] = sum(1 for d in deeper.values() if d['F2'] < 1e-9); out['n_flat_T3'] = sum(1 for d in deeper.values() if d.get('F3', 1) < 1e-9)
    np.save(os.path.join(RES, 'phase10_improper_f1.npy'), F1); json.dump(out, open(os.path.join(RES, 'phase10_improper_f1.json'), 'w'), indent=1); log(out)

def cmd_y2(nproc=12):
    import multiprocessing as mp
    out = os.path.join(RES, 'phase10_improper_y2.npy'); Y = np.full(N8, np.nan)
    with mp.Pool(nproc) as pool:
        for i, (s, v) in enumerate(pool.imap_unordered(y2_job, range(0, N8, 500))):
            Y[s:s + len(v)] = v
            if i % 400 == 0: log(f"y2 batch {i}: max so far {np.nanmax(Y):.4f}")
    np.save(out, Y); log('saved', out)

def ext_index(dec):
    return sum(PERMS.index(tuple(dec['0'] if c == 0 else dec[P9.U3[c - 1]])) * 6 ** c for c in range(8))
def orbit_rep(j):
    return min(ext_index(P9.conj_dec(dec_of(j), Q)) for Q in PERMS)

def sparse_bottoms(L, js, tol=1e-9):
    """pinned bottoms through sparse Lanczos on the fixed sparsity pattern of the reference ordering"""
    import scipy.sparse as sps
    bt = Batched(L); G = bt.frames(js); a, b, ax = bt.a, bt.b, bt.ax; n = bt.n; out = []
    ra = G[:, a, ax, :]; rb = G[:, b, ax, :]; ka, kb = np.abs(ra).argmax(-1), np.abs(rb).argmax(-1)
    sa = np.take_along_axis(ra, ka[..., None], -1)[..., 0]; sb = np.take_along_axis(rb, kb[..., None], -1)[..., 0]
    U = (sa * sb)[..., None, None] * np.einsum('bpij,bpjk->bpik', P9.SIG[ka], P9.SIG[kb])
    r = np.concatenate([2 * a[:, None] + np.array([0, 0, 1, 1]), 2 * b[:, None] + np.array([0, 0, 1, 1])]).ravel()
    c = np.concatenate([2 * b[:, None] + np.array([0, 1, 0, 1]), 2 * a[:, None] + np.array([0, 1, 0, 1])]).ravel()
    for i in range(len(js)):
        v = np.concatenate([U[i].reshape(-1, 4), np.conj(np.transpose(U[i], (0, 2, 1))).reshape(-1, 4)]).ravel()
        H = (24 * sps.identity(2 * n) - sps.csr_matrix((v, (r, c)), shape=(2 * n, 2 * n))).tocsr()
        out.append(float(sla.eigsh(H, k=2, which='SA', tol=tol, ncv=24, return_eigenvectors=False).min()))
    return np.array(out)

def y3_job(js):
    return [(int(j), float(y)) for j, y in zip(js, sparse_bottoms(3, np.array(js)))]

def reps_job(js): return [(int(j), orbit_rep(int(j))) for j in js]

def cmd_y3(nproc=12):
    import multiprocessing as mp
    Y2 = np.load(os.path.join(RES, 'phase10_improper_y2.npy'))
    with mp.Pool(nproc) as pool:
        reps = dict(x for part in pool.imap_unordered(reps_job, [list(range(i, min(i + 5000, N8))) for i in range(0, N8, 5000)]) for x in part)
    R = np.array(sorted(set(reps.values()))); thr = np.median(Y2[R]); sel = R[Y2[R] >= thr]
    log(f"{len(R)} S3-orbit representatives; {len(sel)} with Y2 >= median {thr:.4f}")
    chunks = [sel[i:i + 50].tolist() for i in range(0, len(sel), 50)]; res = {}
    with mp.Pool(nproc) as pool:
        for i, part in enumerate(pool.imap_unordered(y3_job, chunks)):
            res.update(dict(part))
            if i % 100 == 0: log(f"y3 chunk {i}/{len(chunks)}")
    json.dump({'orbit_representatives': int(len(R)), 'screened_top_half_by_Y2': int(len(sel)), 'Y2_median': float(thr), 'Y3': res}, open(os.path.join(RES, 'phase10_improper_y3.json'), 'w'))

def y4_job(j):
    S = P9.build([dec_of(j)] * 4); return int(j), float(sla.eigsh(S['H'], k=2, which='SA', tol=1e-10, return_eigenvectors=False).min())

def y5_job(j):
    S = P9.build([dec_of(j)] * 5); w, V = sla.eigsh(S['H'], k=2, which='SA', tol=1e-11, ncv=48); i = int(np.argmin(w)); v = V[:, i]
    return int(j), float(w[i]), float(np.linalg.norm(S['H'] @ v - w[i] * v))

def cmd_pack(nproc=12):
    """the committed form of stage 1: Y2 of the S3-orbit representatives (all that stage 2 uses) -> phase10_improper_y2_reps.npz;
    the full 6^8 arrays phase10_improper_y2.npy and phase10_improper_f1.npy (13 MB each) are regenerated by y2 and f1"""
    import multiprocessing as mp
    Y2 = np.load(os.path.join(RES, 'phase10_improper_y2.npy'))
    with mp.Pool(nproc) as pool:
        reps = dict(x for part in pool.imap_unordered(reps_job, [list(range(i, min(i + 5000, N8))) for i in range(0, N8, 5000)]) for x in part)
    R = np.array(sorted(set(reps.values()))); np.savez_compressed(os.path.join(RES, 'phase10_improper_y2_reps.npz'), reps=R, Y2=Y2[R]); log(f'{len(R)} representatives packed')

def cmd_y45(nproc=12):
    import multiprocessing as mp
    y3 = {int(k): v for k, v in json.load(open(os.path.join(RES, 'phase10_improper_y3.json')))['Y3'].items()}
    cand = sorted(y3, key=lambda j: -y3[j])[:max(200, len(y3) // 10)]; log(f"Y4 for the top {len(cand)} of {len(y3)} by Y3")
    with mp.Pool(nproc) as pool: y4 = dict(pool.imap_unordered(y4_job, cand, chunksize=8))
    rows = [{'j': j, 'proper': is_proper(j), 'census_index': census_index(j) if is_proper(j) else None, 'Y3': y3[j], 'Y4': y4[j]} for j in cand]
    rows.sort(key=lambda r: -r['Y4']); top = []
    for r in rows:                                                                # drop spectral duplicates (S3 images, gauge copies)
        if any(abs(r['Y4'] - t['Y4']) < 1e-7 for t in top): continue
        top.append(r)
        if len(top) == 10: break
    with mp.Pool(min(nproc, 10)) as pool: y5 = {j: (lam, res) for j, lam, res in pool.imap_unordered(y5_job, [r['j'] for r in top])}
    for r in top:
        r.update({'Y5': y5[r['j']][0], 'Y5_residual': y5[r['j']][1], 'decoration': {str(k): list(x) for k, x in dec_of(r['j']).items()}}); log(r)
    json.dump({'Y4_screened': rows, 'top10_distinct': top}, open(os.path.join(RES, 'phase10_improper_top.json'), 'w'), indent=1)

def frame_structure(dec):
    """the frame substitution on the frames reachable from the identity: (number of frames, irreducible, period, child dets).  All
    children of det -1 give period 2: frames alternate in handedness, every tiling of the hull has uniform handedness, and the two
    halves of the hull are exchanged by a global mirror Q, which leaves every link unchanged ((QM)^T (Q n) = M^T n)"""
    hs = [g for g, _ in P9.ops(dec)]; key = lambda M: tuple(M.ravel().tolist()); fr = {key(np.eye(3, dtype=np.int64)): np.eye(3, dtype=np.int64)}; todo = list(fr.values())
    while todo:
        g = todo.pop()
        for h in hs:
            if key(g @ h) not in fr: fr[key(g @ h)] = g @ h; todo.append(g @ h)
    idx = {k: i for i, k in enumerate(fr)}; n = len(fr); M = np.zeros((n, n), dtype=np.int64)
    for k, g in fr.items():
        for h in hs: M[idx[key(g @ h)], idx[k]] += 1
    P = np.eye(n, dtype=np.int64); reach = np.zeros((n, n), bool); per = 0
    for k in range(1, 3 * n):
        P = np.minimum(P @ M, 1); reach |= P > 0
        if P[0, 0] > 0: per = math.gcd(per, k)
    return n, bool(reach.all()), per, [int(round(np.linalg.det(h))) for h in hs]

def cmd_certify(j):
    """certificates for one extended-space candidate j: frame structure, legal 1-star types, the level-3 bottom from both builders,
    the certified level-4 enclosure (exact Rayleigh above, Higham Cholesky below), Y5 and Y6 with residuals and exact Rayleigh
    upper bounds on E_* -> phase10_improper_certify.jsonl"""
    import phase10_ims as I
    from fractions import Fraction
    import phase10_stageB as B
    dec = dec_of(j); rec = {'j': j, 'proper': is_proper(j), 'decoration': {str(k): list(v) for k, v in dec.items()}}
    nfr, irr, per, dets = frame_structure(dec); types_, n5 = I.phi_closed_types(dec)
    rec.update({'frames': nfr, 'irreducible': irr, 'period': per, 'child_dets': dets, 'n_types1': len(types_), 'n_types1_T5': n5})
    S3 = P9.build([dec] * 3); rec['Y3_builder'] = float(np.linalg.eigvalsh(S3['H'].toarray())[0]); rec['Y3_batched'] = float(sparse_bottoms(3, np.array([j]), tol=1e-12)[0])
    S4 = P9.build([dec] * 4); y4 = P9.lam_min(S4['H']); q4 = P9.rayleigh_upper(S4['H']); mu = Fraction(math.floor((y4 - 1e-6) * 2 ** 20), 2 ** 20)
    rec['Y4_certified'] = [I.cert_lower_sparse(S4['H'], mu), float(q4)]; log(j, rec['Y4_certified'])
    for L in (5, 6):
        S = P9.build([dec] * L); lam, res, v = B.eig_res(S['H'], ncv=40, tol=1e-10); q = B.exact_rayleigh(S['H'], v)
        rec.update({f'Y{L}': lam, f'Y{L}_residual': res, f'Y{L}_upper_exact': f'{q.numerator}/{q.denominator}', f'Y{L}_upper': float(q)}); log(j, L, lam, float(q)); del S, v
    log(rec)
    with open(os.path.join(RES, 'phase10_improper_certify.jsonl'), 'a') as f: f.write(json.dumps(rec) + '\n')

if __name__ == '__main__':
    cmd = sys.argv[1]; globals()[f'cmd_{cmd}'](*[int(x) for x in sys.argv[2:]])
