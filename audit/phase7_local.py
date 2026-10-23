#!/usr/bin/env python3
"""Phase VII (I): is the value of FR30's bulk floor fixed by finite-radius local data?  (deliverables/PHASE7_PROTOCOL.md)

1. Legal R-star types V_R, R = 1..4 (V-B definitions and closure lemma; V_1 by forward orbit, V_2 = Phi_2(V_1), V_3 = Phi_3(V_2),
   V_4 = Phi_4(V_2)), validated against the census of complete R-stars in FR30 supertiles.
2. Certified block lower bounds L_R (cube blocks of side s = R + 1 anchored at c, weight 1/((s-1) s^2)): for every legal R-star
   type, sum over the (s+1)^3 - 1 blocks meeting the centre tile of a certified mu_c <= lambda_min(k_c); L_R = min / ((s-1)s^2).
   L_R is a lower bound on inf spec(24 - A_U) for EVERY tiling all of whose R-stars are legal (in particular FR30).
   Certificates: rigorous floating-point Cholesky bound (Higham 2002, Thm 10.3) for every block, exact Bareiss/Sylvester over Z[i]
   on a sample (and on all blocks for R = 2, which must reproduce V-B's 72147403/18000000).
3. Radius-R legality of the V-A periodic approximants P_k (level-k FR30 supertile on 2^k Lambda_7), k = 1..5, R = 1..4.
Usage: python -u -I audit/phase7_local.py [stage ...]   stages: types bounds approximants   -> audit/results/phase7_local*.json
"""
import os, sys, time, itertools, collections, json, types
from fractions import Fraction
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); RES = os.path.join(HERE, 'results')
try:
    import resource  # noqa: F401
except ImportError:
    sys.modules['resource'] = types.SimpleNamespace(getrusage=lambda *a: types.SimpleNamespace(ru_maxrss=0), RUSAGE_SELF=0)
import numpy as np
from independent_clifford_q8_audit import FR30, U3, perm_mat, clifford_link
T0 = time.time()
def log(*a): print(f"[{time.time()-T0:7.0f}s]", *a, flush=True)

# ------------------------------------------------------------------ substitution and frame data (as in phase5b_e_radius2_bound)
def make_ops(dec):
    ops = [(perm_mat(dec['0']), np.array([1, 1, 1]))]
    for v in U3: ops.append((np.diag([1 - 2 * v[0], 1 - 2 * v[1], 1 - 2 * v[2]]) @ perm_mat(dec[v]), 4 * np.array(v)))
    return ops
OPS = make_ops(FR30); GOPS = np.array([g for g, t in OPS]); TOPS = np.array([t for g, t in OPS])
LB = np.array([[2 * u[0] + 1, 2 * u[1] + 1, 2 * u[2] + 1] for u in U3])
I3 = np.eye(3, dtype=int)
def key(M): return tuple(int(x) for x in np.asarray(M).ravel())
Gs = [I3.copy()]; gidx = {key(I3): 0}; fr = [I3]
while fr:
    new = []
    for M in fr:
        for g in GOPS:
            Pm = M @ g
            if key(Pm) not in gidx: gidx[key(Pm)] = len(Gs); Gs.append(Pm); new.append(Pm)
    fr = new
Gs = np.array(Gs); NG = len(Gs); assert NG == 24
MULT = np.array([[gidx[key(Gs[i] @ Gs[j])] for j in range(NG)] for i in range(NG)]); INV = np.array([gidx[key(Gs[i].T)] for i in range(NG)])
LINKGI = np.zeros((NG, NG, 3, 2, 2, 2), np.int64)
for a in range(NG):
    for b in range(NG):
        for ax in range(3):
            nv = np.zeros(3, int); nv[ax] = 1; C = clifford_link(Gs[a], Gs[b], nv)
            LINKGI[a, b, ax, ..., 0] = np.rint(C.real); LINKGI[a, b, ax, ..., 1] = np.rint(C.imag)
def Lr(R): return [l for l in itertools.product(range(-R, R + 2), repeat=3) if l != (R + 1, R + 1, R + 1)]
LODD = {R: 2 * np.array(Lr(R)) + 1 for R in (1, 2, 3, 4)}
for R in (1, 2, 3, 4): assert len(LODD[R]) == (2 * R + 2) ** 3 - 1
R_ENC = 24; K_ENC = 2 * R_ENC + 1
def encode(rf, rel):
    assert (np.abs(rel) <= R_ENC).all()
    return ((rf * K_ENC + rel[..., 0] + R_ENC) * K_ENC + rel[..., 1] + R_ENC) * K_ENC + rel[..., 2] + R_ENC
def decode(code):
    code = int(code); dz = code % K_ENC - R_ENC; code //= K_ENC; dy = code % K_ENC - R_ENC; code //= K_ENC
    dx = code % K_ENC - R_ENC; return code // K_ENC, (dx, dy, dz)
def gen_poses(level):
    G = I3[None].astype(np.int64); T = np.zeros((1, 3), np.int64)
    for _ in range(level):
        G2 = np.einsum('nij,cjk->ncik', G, GOPS).reshape(-1, 3, 3); T2 = (2 * T[:, None, :] + np.einsum('nij,cj->nci', G, TOPS)).reshape(-1, 3)
        G, T = G2, T2
    return G.astype(np.int8), T.astype(np.int64)
_LUT = None
def frame_index(G):
    global _LUT
    if _LUT is None:
        _LUT = np.full(3 ** 9, -1, np.int16)
        for i in range(NG): _LUT[int((((Gs[i].ravel() + 1) * (3 ** np.arange(9))).sum()))] = i
    flat = np.asarray(G).reshape(len(G), 9).astype(np.int64); out = _LUT[((flat + 1) * (3 ** np.arange(9))).sum(1)]; assert (out >= 0).all()
    return out.astype(np.int64)
def cubes_of_poses(G, T, odd=LB):
    return (np.einsum('nij,kj->nki', np.asarray(G, np.int64), odd) + 2 * np.asarray(T, np.int64)[:, None, :] - 1) // 2
def owner_grid(level, G, T):
    N = 2 ** (level + 1); grid = np.full((N, N, N), -1, np.int32)
    for s in range(0, len(G), 65536):
        cubes = cubes_of_poses(G[s:s + 65536], T[s:s + 65536]); flat = cubes.reshape(-1, 3)
        grid[flat[:, 0], flat[:, 1], flat[:, 2]] = np.repeat(np.arange(s, s + len(cubes), dtype=np.int32), 7)
    return grid
def lookup(grid, P):
    N = grid.shape[0]; inside = ((P >= 0) & (P < N)).all(-1); Pc = np.where(inside[..., None], P, 0)
    return np.where(inside, grid[Pc[..., 0], Pc[..., 1], Pc[..., 2]], -1)
def star_types(G, T, grid, odd, chunk=4096):
    N = len(G); fi = frame_index(G); cnt = collections.Counter(); ncomplete = 0
    for s in range(0, N, chunk):
        sl = slice(s, min(N, s + chunk)); O = lookup(grid, cubes_of_poses(G[sl], T[sl], odd))
        comp = (O >= 0).all(1); idx = np.nonzero(comp)[0]; ncomplete += len(idx)
        if len(idx) == 0: continue
        Oc = O[idx]; a = idx + s; rf = MULT[INV[fi[a]][:, None], fi[Oc]]
        rel = np.einsum('nji,nkj->nki', np.asarray(G[a], np.int64), T[Oc] - T[a][:, None, :])
        codes = np.sort(encode(rf, rel), axis=1)
        for row in codes: cnt[frozenset(int(x) for x in row)] += 1
    return cnt, ncomplete
def poses_from_key(k):
    poses = [(Gs[decode(c)[0]].copy(), np.array(decode(c)[1])) for c in sorted(k)]
    center = [i for i, (g, t) in enumerate(poses) if key(g) == key(I3) and tuple(t) == (0, 0, 0)]; assert len(center) == 1
    return poses, center[0]
def owner_dict(poses):
    own = {}
    for a, (g, t) in enumerate(poses):
        for c in cubes_of_poses(g[None], t[None])[0]:
            c = tuple(int(x) for x in c); assert c not in own; own[c] = a
    return own
def star_key_in_patch(poses, own, center, odd):
    g0, t0 = poses[center]; mem = set()
    for c in cubes_of_poses(g0[None], t0[None], odd)[0]:
        o = own.get(tuple(int(x) for x in c))
        if o is None: return None
        mem.add(o)
    return frozenset(int(encode(gidx[key(g0.T @ poses[b][0])], g0.T @ (poses[b][1] - t0))) for b in mem)
def inflate(poses): return [(g @ gg, 2 * t + g @ tt) for g, t in poses for gg, tt in OPS]
def Phi_r(k, odd_out):
    poses, center = poses_from_key(k); fine = inflate(poses); own = owner_dict(fine); out = []
    for c in range(8):
        kk = star_key_in_patch(fine, own, 8 * center + c, odd_out); assert kk is not None, 'closure lemma violated'; out.append(kk)
    return out

# ------------------------------------------------------------------ 1. legal types
def legal_types(census_level=6):
    G4, T4 = gen_poses(4); grid4 = owner_grid(4, G4, T4); cnt1, _ = star_types(G4, T4, grid4, LODD[1])
    seed = max(cnt1, key=cnt1.get); V = {1: {seed}}; frontier = [seed]
    while frontier:
        new = []
        for k in frontier:
            for kk in Phi_r(k, LODD[1]):
                if kk not in V[1]: V[1].add(kk); new.append(kk)
        frontier = new
    V[2] = {kk for k in V[1] for kk in Phi_r(k, LODD[2])}
    V[3] = {kk for k in V[2] for kk in Phi_r(k, LODD[3])}
    V[4] = {kk for k in V[2] for kk in Phi_r(k, LODD[4])}
    out = {'sizes': {R: len(V[R]) for R in V}}
    log(f"legal types: |V_1| = {len(V[1])}, |V_2| = {len(V[2])}, |V_3| = {len(V[3])}, |V_4| = {len(V[4])}")
    assert len(V[1]) == 72 and len(V[2]) == 165
    # closure checks: Phi_RR(V_R) subset V_R (the R-star of a child lies in sigma(ceil(R/2)-star) subset sigma(R-star))
    for R in (3, 4):
        clo = all(kk in V[R] for k in V[R] for kk in Phi_r(k, LODD[R])); out[f'closed_{R}'] = clo; log(f"Phi_{R}{R}(V_{R}) subset V_{R}: {clo}")
    # census validation
    G, T = gen_poses(census_level); grid = owner_grid(census_level, G, T)
    for R in (1, 2, 3, 4):
        t0 = time.time(); cnt, c = star_types(G, T, grid, LODD[R])
        out[f'census_L{census_level}_R{R}'] = {'complete': c, 'distinct': len(cnt), 'subset': set(cnt) <= V[R], 'equal': set(cnt) == V[R]}
        log(f"census T_{census_level} R={R}: {c} complete stars, {len(cnt)} types, subset of V_{R}: {set(cnt) <= V[R]}, equal: {set(cnt) == V[R]} ({time.time()-t0:.0f}s)")
    return V, out

# ------------------------------------------------------------------ 2. block bounds
def block_form(block, own, fidx):
    cs = set(block); tiles = sorted({own[q] for q in cs}); loc = {t: i for i, t in enumerate(tiles)}; n = len(tiles)
    Re = np.zeros((2 * n, 2 * n), np.int64); Im = np.zeros((2 * n, 2 * n), np.int64)
    for q in cs:
        for ax in range(3):
            q2 = (q[0] + (ax == 0), q[1] + (ax == 1), q[2] + (ax == 2))
            if q2 not in cs: continue
            t1, t2 = own[q], own[q2]
            if t1 == t2: continue
            C = LINKGI[fidx[t1], fidx[t2], ax]; a, b = loc[t1], loc[t2]
            for i in range(2): Re[2*a+i, 2*a+i] += 1; Re[2*b+i, 2*b+i] += 1
            Re[2*a:2*a+2, 2*b:2*b+2] -= C[..., 0]; Im[2*a:2*a+2, 2*b:2*b+2] -= C[..., 1]
            Re[2*b:2*b+2, 2*a:2*a+2] -= C[..., 0].T; Im[2*b:2*b+2, 2*a:2*a+2] += C[..., 1].T
    assert (Re == Re.T).all() and (Im == -Im.T).all()
    return Re, Im, n
def realform(Re, Im): return np.block([[Re, -Im], [Im, Re]]).astype(float)
U_ROUND = 2.0 ** -53
def higham_certify(Re, Im, lam):
    """rigorous lower bound mu <= lambda_min(Re + i Im) as a Fraction: unblocked Cholesky of A - mu' I (A = real form, exact in
    float64), then lambda_min(A) >= mu' - gamma_{N+1} || |R|^T |R| ||_inf (Higham 2002, Thm 10.3), inflated for rounding."""
    A = realform(Re, Im); N = A.shape[0]
    if N == 0: return Fraction(0)
    for shift in (1e-7, 1e-5, 1e-3, 1e-2):
        mup = np.floor((lam - shift) * 2 ** 20) / 2 ** 20
        if mup <= 0: return Fraction(0)
        B = A - mup * np.eye(N); R = np.zeros_like(B); ok = True
        for j in range(N):
            s = B[j, j] - R[:j, j] @ R[:j, j]
            if not s > 0: ok = False; break
            R[j, j] = np.sqrt(s)
            if j + 1 < N: R[j, j + 1:] = (B[j, j + 1:] - R[:j, j] @ R[:j, j + 1:]) / R[j, j]
        if not ok: continue
        gam = (N + 1) * U_ROUND / (1 - (N + 1) * U_ROUND)
        Mabs = np.abs(R).T @ np.abs(R); rowmax = float(np.max(Mabs.sum(1)))
        eps = gam * rowmax * (1 + 4 * N * U_ROUND) * 1.0001 + 1e-300            # inflation covers the rounding of |R|^T|R| and its row sums
        return Fraction(mup) - Fraction(eps)
    return Fraction(0)
def bareiss_posdef(Re, Im, p, q):
    """exact Sylvester test (V-B routine): is q (Re + i Im) - p I positive definite?"""
    n = Re.shape[0]; A = [[(q * int(Re[i, j]) - (p if i == j else 0), q * int(Im[i, j])) for j in range(n)] for i in range(n)]; prev = 1
    for k in range(n):
        pr, pim = A[k][k]; assert pim == 0
        if pr <= 0: return False
        for i in range(k + 1, n):
            air, aii = A[i][k]
            for j in range(k + 1, n):
                xr, xi = A[i][j]; bkr, bki = A[k][j]
                nr = pr * xr - (air * bkr - aii * bki); ni = pr * xi - (air * bki + aii * bkr)
                qr, rr = divmod(nr, prev); qi, ri = divmod(ni, prev); assert rr == 0 and ri == 0
                A[i][j] = (qr, qi)
        prev = pr
    return True
def canon_block(block, own, fidx, c, s):
    """rotation-canonical signature of a block (offsets doubled about the block centre so rotations act on integers)."""
    offs = [tuple(2 * (q[i] - c[i]) - (s - 1) for i in range(3)) for q in block]; owners = [own[q] for q in block]; frames = [int(fidx[t]) for t in owners]
    best = None
    for gi in range(NG):
        g = Gs[gi]; rot = [tuple(int(x) for x in g @ np.array(o)) for o in offs]; order = sorted(range(len(block)), key=lambda t: rot[t])
        lab = {}; sig = []
        for t in order: lab.setdefault(owners[t], len(lab)); sig.append((lab[owners[t]], int(MULT[gi, frames[t]])))
        sig = tuple(sig)
        if best is None or sig < best: best = sig
    return best
def block_bound(V, R, exact_sample=200, exact_all=False, seed=0):
    s = R + 1; W = (s - 1) * s * s; box = list(itertools.product(range(s), repeat=3))
    sig_data = {}; type_sigs = {}; t0 = time.time()
    for k in V[R]:
        poses, center = poses_from_key(k); own = owner_dict(poses); fidx = np.array([gidx[key(g)] for g, t in poses])
        ccubes = [tuple(int(x) for x in c) for c in cubes_of_poses(poses[center][0][None], poses[center][1][None])[0]]
        anchors = {(q[0] - o[0], q[1] - o[1], q[2] - o[2]) for q in ccubes for o in box}
        assert len(anchors) == (s + 1) ** 3 - 1
        sigs = []
        for c in sorted(anchors):
            block = [(c[0] + o[0], c[1] + o[1], c[2] + o[2]) for o in box]
            assert all(q in own for q in block), 'block not inside the R-star patch'
            sig = canon_block(block, own, fidx, c, s)
            if sig not in sig_data:
                Re, Im, n = block_form(block, own, fidx); lam = float(np.linalg.eigvalsh(Re + 1j * Im)[0]) if n else 0.0
                sig_data[sig] = [Re, Im, lam, None]
            sigs.append(sig)
        type_sigs[k] = sigs
    log(f"R={R}: {len(V[R])} types x {(s+1)**3-1} blocks, {len(sig_data)} distinct signatures, max dim {max(v[0].shape[0] for v in sig_data.values())} ({time.time()-t0:.0f}s)")
    t0 = time.time()
    for sig, v in sig_data.items(): v[3] = higham_certify(v[0], v[1], v[2])
    log(f"R={R}: Higham certificates done ({time.time()-t0:.0f}s); max |lam - mu| = {max(v[2] - float(v[3]) for v in sig_data.values()):.2e}")
    # exact cross-check (Bareiss) on a sample, or on all
    rng = np.random.default_rng(seed); keys = list(sig_data); pick = keys if exact_all else [keys[i] for i in rng.choice(len(keys), min(exact_sample, len(keys)), replace=False)]
    t0 = time.time(); agree = 0; reject_above = 0
    for sg in pick:
        Re, Im, lam, mu = sig_data[sg]
        if mu <= 0: continue
        ok = bareiss_posdef(Re, Im, mu.numerator, mu.denominator); agree += ok
        above = Fraction(int(np.floor((lam + 1e-6) * 2 ** 20)) + 1, 2 ** 20); reject_above += not bareiss_posdef(Re, Im, above.numerator, above.denominator)
    log(f"R={R}: exact Bareiss confirms mu_c on {agree}/{len(pick)} sampled blocks and rejects lambda+1e-6 on {reject_above}/{len(pick)} ({time.time()-t0:.0f}s)")
    S_cert = {k: sum((sig_data[sg][3] for sg in sigs), Fraction(0)) for k, sigs in type_sigs.items()}
    S_float = {k: sum(sig_data[sg][2] for sg in sigs) for k, sigs in type_sigs.items()}
    kmin = min(S_cert, key=S_cert.get); L = S_cert[kmin] / W
    res = {'R': R, 'block_side': s, 'weight': W, 'types': len(V[R]), 'signatures': len(sig_data), 'max_dim': int(max(v[0].shape[0] for v in sig_data.values())),
           'L_R_certified': f'{L.numerator}/{L.denominator}', 'L_R_float_value': float(L), 'L_R_float_uncertified': min(S_float.values()) / W,
           'S_over_W_median': float(np.median([float(v) for v in S_cert.values()]) / W), 'S_over_W_max': float(max(S_cert.values()) / W),
           'exact_sample_confirmed': f'{agree}/{len(pick)}', 'exact_sample_rejects_lambda_plus': f'{reject_above}/{len(pick)}',
           'block_lambda_min_range': [float(min(v[2] for v in sig_data.values())), float(max(v[2] for v in sig_data.values()))]}
    log(f"R={R}: CERTIFIED L_R = {float(L):.6f}  (float {res['L_R_float_uncertified']:.6f}; median {res['S_over_W_median']:.4f}, max {res['S_over_W_max']:.4f})")
    return res

def identity_check(R, level=3):
    """sum over anchored s-blocks of k_c equals (s-1)s^2 (24 - A) on rows of tiles whose blocks all lie inside T_level."""
    s = R + 1; W = (s - 1) * s * s; G, T = gen_poses(level); grid = owner_grid(level, G, T); n = len(G); fidx = frame_index(G)
    own = {}
    for a in range(n):
        for c in cubes_of_poses(G[a:a+1], T[a:a+1])[0]: own[tuple(int(x) for x in c)] = a
    box = list(itertools.product(range(s), repeat=3)); Nb = 2 ** (level + 1)
    K = np.zeros((2 * n, 2 * n), complex); full = set()
    for c in itertools.product(range(-1, Nb), repeat=3):
        block = [(c[0] + o[0], c[1] + o[1], c[2] + o[2]) for o in box]
        if not all(q in own for q in block): continue
        full.add(c); Re, Im, m = block_form(block, own, fidx); tiles = sorted({own[q] for q in block})
        for i, ti in enumerate(tiles):
            for j, tj in enumerate(tiles): K[2*ti:2*ti+2, 2*tj:2*tj+2] += (Re + 1j * Im)[2*i:2*i+2, 2*j:2*j+2]
    from independent_clifford_q8_audit import tiles_at_level, panel_edges
    from phase5a_controls import clifford_links, build_H
    tl = tiles_at_level(FR30, level); _, ed = panel_edges(tl); Hm = build_H(len(tl), ed, clifford_links(tl, ed), np.full(len(tl), 24.0)).toarray()
    good = [a for a in range(n) if all((q[0] - o[0], q[1] - o[1], q[2] - o[2]) in full for q in (tuple(int(x) for x in cc) for cc in cubes_of_poses(G[a:a+1], T[a:a+1])[0]) for o in box)]
    rows = np.array([2 * a + r for a in good for r in range(2)])
    dev = float(np.abs(K[rows] / W - Hm[rows]).max()) if len(rows) else float('nan')
    log(f"identity check R={R}, s={s}: {len(good)} interior tiles of T_{level}; max |(1/{W}) sum_c K_c - (24 - A)| = {dev:.1e}")
    return {'R': R, 'interior_tiles': len(good), 'max_dev': dev}

# ------------------------------------------------------------------ 3. approximant legality
def approximant_legality(V, k, Rs=(1, 2, 3, 4)):
    """R-star types of every tile of P_k (level-k FR30 supertile on 2^k Lambda_7, V-A construction), checked against V_R."""
    from phase5a_periodic_control import owner_of_cube
    G, T = gen_poses(k); n = len(G); N = 2 ** k; grid = owner_grid(k, G, T); fi = frame_index(G)
    def owner(cubes):
        """global cube -> (tile index, translation d of its supertile copy)"""
        out_t = np.empty(len(cubes), np.int64); out_d = np.empty((len(cubes), 3), np.int64)
        for i, c in enumerate(cubes):
            V_ = np.floor_divide(c, N); d = N * owner_of_cube(V_); loc = c - d
            t = grid[loc[0], loc[1], loc[2]]; assert t >= 0; out_t[i] = t; out_d[i] = d
        return out_t, out_d
    res = {}
    for R in Rs:
        illegal = 0; t0 = time.time()
        for a in range(n):
            cubes = cubes_of_poses(G[a:a+1], T[a:a+1], LODD[R])[0]; tb, db = owner(cubes)
            rel = np.asarray(G[a], np.int64).T @ (T[tb] + db - T[a]).T
            codes = encode(MULT[INV[fi[a]], fi[tb]], rel.T)
            if frozenset(int(x) for x in codes) not in V[R]: illegal += 1
        res[R] = {'tiles': n, 'illegal': illegal, 'illegal_fraction': illegal / n}
        log(f"P_{k}: R={R}: {illegal}/{n} tiles with an illegal R-star ({illegal/n:.4f})  ({time.time()-t0:.0f}s)")
    return res

if __name__ == '__main__':
    stages = sys.argv[1:] or ['types', 'bounds', 'approximants']
    V, tout = legal_types()
    out = {'types': tout}
    if 'bounds' in stages:
        out['identity'] = [identity_check(R) for R in (2, 3)]
        out['bounds'] = {}
        for R in (2, 3, 4):
            out['bounds'][R] = block_bound(V, R, exact_sample={3: 60, 4: 20}.get(R, 200), exact_all=(R == 2)); json.dump(out, open(os.path.join(RES, 'phase7_local.json'), 'w'), indent=1, default=str)
    if 'approximants' in stages:
        out['approximants'] = {k: approximant_legality(V, k) for k in (1, 2, 3, 4)}
    json.dump(out, open(os.path.join(RES, 'phase7_local.json'), 'w'), indent=1, default=str)
    log('done')
