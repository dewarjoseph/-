"""
Phase 5a / referee check C2 of Task B3 (audit/phase5a_star_closure_lower_bound.py):
   claim  E_bulk = inf spec(H_omega) >= 3137451/2000000 = 1.5687255.

Everything below is re-derived with independent code; only the repository primitives tiles_at_level /
panel_edges / clifford_link / q8label (audit/independent_clifford_q8_audit.py) are imported, so that H is built
with exactly the conventions of the claim.

Stages (select with argv, default all):
  2  decomposition identity  <psi,H psi> = (1/4) sum_e h_e(psi)  on T_3, exact matrix comparison
  3  72 star types re-extracted from T_4, T_5 (own vectorised owner-grid code) + own closure orbit;
     lambda_min(h_e) in float, star sums, own exact rational LDL^* certificate for every signature
  4  completeness attack: complete vertex stars of T_6 (and T_7 if memory allows), rotated / translated copies
  5  LOBPCG ground state of pinned T_5 (upper bound) and the per-star diagnostic of the slack
  6  cheap improvements (float only, uncertified): vertex-block (2x2x2) decomposition, convex mixing with
     the edge decomposition, and a cube-centred 3x3x3-block decomposition needing 2-stars (from T_5/T_6)
Run from the repository root:  OMP_NUM_THREADS=1 python3 -u -I audit/phase5a_c2_lower_bound_check.py [stages]
"""
import os, sys, time, itertools, collections
from fractions import Fraction
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from independent_clifford_q8_audit import FR30, U3, perm_mat, tiles_at_level, panel_edges, clifford_link, q8label

STAGES = set(int(c) for c in (sys.argv[1] if len(sys.argv) > 1 else "23456"))
OUT = []
T_START = time.time()
def say(*a):
    s = " ".join(str(x) for x in a); print(s, flush=True); OUT.append(s)
def flush():
    with open(os.path.join(HERE, 'results', 'phase5a_c2_lower_bound_check' + (('_stages' + sys.argv[1]) if len(sys.argv) > 1 else '') + '.txt'), 'w') as f:
        f.write("\n".join(OUT) + "\n")

# ----------------------------------------------------------------------------------------------- basic data
ops = [(perm_mat(FR30['0']), np.array([1, 1, 1]))]
for v in U3:
    ops.append((np.diag([1 - 2 * v[0], 1 - 2 * v[1], 1 - 2 * v[2]]) @ perm_mat(FR30[v]), 4 * np.array(v)))
GOPS = np.array([g for g, t in ops]); TOPS = np.array([t for g, t in ops])
LB = np.array([[2 * u[0] + 1, 2 * u[1] + 1, 2 * u[2] + 1] for u in U3])          # 7 odd vectors = local cube centers*2
I3 = np.eye(3, dtype=int)
def key(M): return tuple(int(x) for x in np.asarray(M).ravel())

# frame group (24 elements), multiplication / inverse tables
Gs = [I3.copy()]; gidx = {key(I3): 0}; fr = [I3]
while fr:
    new = []
    for M in fr:
        for g in GOPS:
            P = M @ g
            if key(P) not in gidx: gidx[key(P)] = len(Gs); Gs.append(P); new.append(P)
    fr = new
Gs = np.array(Gs); NG = len(Gs)
MULT = np.array([[gidx[key(Gs[i] @ Gs[j])] for j in range(NG)] for i in range(NG)])
INV = np.array([gidx[key(Gs[i].T)] for i in range(NG)])
assert NG == 24
# link table: LINK[fa, fb, axis] = clifford_link(Gs[fa], Gs[fb], e_axis)   (sign of the normal is irrelevant)
LINK = np.zeros((NG, NG, 3, 2, 2), complex)
for a in range(NG):
    for b in range(NG):
        for ax in range(3):
            n = np.zeros(3, int); n[ax] = 1
            LINK[a, b, ax] = clifford_link(Gs[a], Gs[b], n)
            assert np.allclose(LINK[a, b, ax], clifford_link(Gs[a], Gs[b], -n))
Q8 = ['+1', '-1', '+i', '-i', '+j', '-j', '+k', '-k']
LINKLAB = np.array([[[Q8.index(q8label(LINK[a, b, ax])) for ax in range(3)] for b in range(NG)] for a in range(NG)])

# local neighbourhood of the chair: all local cubes within Chebyshev distance 1 of a chair cube
L1 = [l for l in itertools.product((-1, 0, 1, 2), repeat=3) if l != (2, 2, 2)]
assert len(L1) == 63
L1ODD = 2 * np.array(L1) + 1
L2 = [l for l in itertools.product((-2, -1, 0, 1, 2, 3), repeat=3) if l != (3, 3, 3)]
assert len(L2) == 215
L2ODD = 2 * np.array(L2) + 1
R_ENC = 16; K_ENC = 2 * R_ENC + 1

def gen_poses(level):
    """vectorised version of tiles_at_level: returns G (N,3,3) int, T (N,3) int, same order."""
    G = I3[None].astype(np.int64); T = np.zeros((1, 3), np.int64)
    for _ in range(level):
        G2 = np.einsum('nij,cjk->ncik', G, GOPS).reshape(-1, 3, 3)
        T2 = (2 * T[:, None, :] + np.einsum('nij,cj->nci', G, TOPS)).reshape(-1, 3)
        G, T = G2, T2
    return G.astype(np.int8), T.astype(np.int32)

def frame_index(G):
    """index in Gs of each frame in G (N,3,3)."""
    flat = G.reshape(len(G), 9).astype(np.int64)
    code = ((flat + 1) * (3 ** np.arange(9))).sum(1)
    table = {int((((Gs[i].ravel() + 1) * (3 ** np.arange(9))).sum())): i for i in range(NG)}
    lut = np.full(3 ** 9, -1, np.int8)
    for c, i in table.items(): lut[c] = i
    out = lut[code]; assert (out >= 0).all()
    return out.astype(np.int64)

def cubes_of_poses(G, T, odd=LB):
    """global cube corners (N, k, 3) for the local odd vectors `odd` (k,3)."""
    return (np.einsum('nij,kj->nki', G.astype(np.int64), odd) + 2 * T[:, None, :].astype(np.int64) - 1) // 2

def owner_grid(level, G, T):
    N = 2 ** (level + 1)
    grid = np.full((N, N, N), -1, np.int32)
    for s in range(0, len(G), 65536):                     # chunked: keeps peak memory small for T_7
        cubes = cubes_of_poses(G[s:s+65536], T[s:s+65536])
        assert cubes.min() >= 0 and cubes.max() < N
        flat = cubes.reshape(-1, 3)
        grid[flat[:, 0], flat[:, 1], flat[:, 2]] = np.repeat(np.arange(s, s + len(cubes), dtype=np.int32), 7)
    assert (grid >= 0).sum() == 7 * len(G), "overlapping cubes"
    return grid

def lookup(grid, P):
    N = grid.shape[0]
    inside = ((P >= 0) & (P < N)).all(-1)
    Pc = np.where(inside[..., None], P, 0)
    o = grid[Pc[..., 0], Pc[..., 1], Pc[..., 2]]
    return np.where(inside, o, -1)

def encode(rf, rel):
    """integer code of a relative pose (frame index, relative translation)."""
    assert (np.abs(rel) <= R_ENC).all()
    return ((rf * K_ENC + rel[..., 0] + R_ENC) * K_ENC + rel[..., 1] + R_ENC) * K_ENC + rel[..., 2] + R_ENC
def decode(code):
    code = int(code); dz = code % K_ENC - R_ENC; code //= K_ENC; dy = code % K_ENC - R_ENC; code //= K_ENC
    dx = code % K_ENC - R_ENC; rf = code // K_ENC
    return rf, (dx, dy, dz)

def star_types(level, G, T, grid, odd=L1ODD, chunk=16384, return_tile_keys=False):
    """complete r-stars (r=1 for L1ODD, r=2 for L2ODD) of all tiles; returns dict key->representative tile,
    number complete, number incomplete, and (optionally) the per-tile key index."""
    N = len(G); fi = frame_index(G)
    types = {}; ncomplete = 0; tile_key = np.full(N, -1, np.int64) if return_tile_keys else None
    keylist = []
    for s in range(0, N, chunk):
        sl = slice(s, min(N, s + chunk))
        P = cubes_of_poses(G[sl], T[sl], odd)                       # (n, k, 3)
        O = lookup(grid, P)                                         # (n, k)
        comp = (O >= 0).all(1)
        idx = np.nonzero(comp)[0]; ncomplete += len(idx)
        if len(idx) == 0: continue
        Oc = O[idx]; a = idx + s
        rf = MULT[INV[fi[a]][:, None], fi[Oc]]                      # (n,k) relative frame index
        rel = np.einsum('nji,nkj->nki', G[a].astype(np.int64), T[Oc].astype(np.int64) - T[a][:, None, :].astype(np.int64))
        codes = np.sort(encode(rf, rel), axis=1)
        uniq, first, inv = np.unique(codes, axis=0, return_index=True, return_inverse=True)
        loc = {}
        for r, row in enumerate(uniq):
            k = frozenset(int(c) for c in row)
            if k not in types: types[k] = int(a[first[r]])
            loc[r] = k
        if return_tile_keys:
            keylist_index = {k: i for i, k in enumerate(keylist)}
            for r in range(len(uniq)):
                k = loc[r]
                if k not in keylist_index: keylist_index[k] = len(keylist); keylist.append(k)
            tile_key[a] = np.array([keylist_index[loc[r]] for r in inv.ravel()])
    return types, ncomplete, N - ncomplete, (tile_key, keylist)

def poses_from_key(k):
    """star patch (list of (G, T)) with the center at (I, 0); returns poses, center index."""
    poses = []
    for c in sorted(k):
        rf, d = decode(c); poses.append((Gs[rf].copy(), np.array(d)))
    center = [i for i, (g, t) in enumerate(poses) if key(g) == key(I3) and tuple(t) == (0, 0, 0)]
    assert len(center) == 1
    return poses, center[0]

def owner_dict(poses):
    own = {}
    for a, (g, t) in enumerate(poses):
        for c in cubes_of_poses(g[None], t[None])[0]:
            c = tuple(int(x) for x in c); assert c not in own; own[c] = a
    return own

def star_key_in_patch(poses, own, center, odd=L1ODD):
    g0, t0 = poses[center]
    P = cubes_of_poses(g0[None], t0[None], odd)[0]
    mem = set()
    for c in P:
        o = own.get(tuple(int(x) for x in c))
        if o is None: return None
        mem.add(o)
    codes = set()
    for b in mem:
        gb, tb = poses[b]
        codes.add(int(encode(gidx[key(g0.T @ gb)], g0.T @ (tb - t0))))
    return frozenset(codes)

def Phi_own(k):
    """own implementation of the collared substitution on a 1-star type."""
    poses, center = poses_from_key(k)
    fine = [(g @ gg, 2 * t + g @ tt) for g, t in poses for gg, tt in ops]
    own = owner_dict(fine)
    out = []
    for c in range(8):
        kk = star_key_in_patch(fine, own, 8 * center + c)
        assert kk is not None, "closure lemma violated"
        out.append(kk)
    return out

# ----------------------------------------------------------------------------------------------- plaquette forms
CYC = [(0, 0), (1, 0), (1, 1), (0, 1)]
def edges_touching(cubes):
    """all lattice edges (axis k, lattice point p) that are edges of one of the given cubes; with the 4 cubes
    around each edge in cyclic order."""
    seen = {};
    for c in cubes:
        for k in range(3):
            i, j = [x for x in range(3) if x != k]
            for di, dj in itertools.product((0, 1), repeat=2):
                p = list(c); p[i] += di; p[j] += dj; p = tuple(p)
                if (k, p) in seen: continue
                cyc = []
                for a, b in CYC:
                    q = list(p); q[i] -= a; q[j] -= b; cyc.append(tuple(q))
                seen[(k, p)] = cyc
    return seen

def h_form(cyc, own, fidx):
    """h_e as a Hermitian matrix on the distinct tiles around the edge; cubes may be missing (owner None)."""
    tiles = [own.get(q) for q in cyc]
    labels = sorted(set(t for t in tiles if t is not None)); loc = {t: i for i, t in enumerate(labels)}
    n = len(labels); H = np.zeros((2 * n, 2 * n), complex); links = []
    for s in range(4):
        q1, q2 = cyc[s], cyc[(s + 1) % 4]; t1, t2 = tiles[s], tiles[(s + 1) % 4]
        if t1 is None or t2 is None or t1 == t2: links.append(8 if t1 == t2 else 9); continue
        ax = int(np.nonzero(np.array(q2) - np.array(q1))[0][0])
        C = LINK[fidx[t1], fidx[t2], ax]
        a, b = loc[t1], loc[t2]
        H[2*a:2*a+2, 2*a:2*a+2] += np.eye(2); H[2*b:2*b+2, 2*b:2*b+2] += np.eye(2)
        H[2*a:2*a+2, 2*b:2*b+2] -= C; H[2*b:2*b+2, 2*a:2*a+2] -= C.conj().T
        links.append(int(LINKLAB[fidx[t1], fidx[t2], ax]))
    pattern = tuple(loc[t] if t is not None else -1 for t in tiles)
    return H, labels, (pattern, tuple(links))

def block_form(cubes_block, own, fidx):
    """quadratic form of all inter-tile faces inside a set of cubes (list of tuples)."""
    cs = set(cubes_block); tiles = sorted(set(own[q] for q in cs if q in own)); loc = {t: i for i, t in enumerate(tiles)}
    n = len(tiles); H = np.zeros((2 * n, 2 * n), complex)
    for q in cs:
        if q not in own: continue
        for ax in range(3):
            q2 = list(q); q2[ax] += 1; q2 = tuple(q2)
            if q2 not in cs or q2 not in own: continue
            t1, t2 = own[q], own[q2]
            if t1 == t2: continue
            C = LINK[fidx[t1], fidx[t2], ax]; a, b = loc[t1], loc[t2]
            H[2*a:2*a+2, 2*a:2*a+2] += np.eye(2); H[2*b:2*b+2, 2*b:2*b+2] += np.eye(2)
            H[2*a:2*a+2, 2*b:2*b+2] -= C; H[2*b:2*b+2, 2*a:2*a+2] -= C.conj().T
    return H, tiles

def lam_min(H):
    return 0.0 if H.shape[0] == 0 else float(np.linalg.eigvalsh(H)[0])

# exact LDL^* (own implementation, Gaussian-rational arithmetic as pairs of Fractions)
def exact_pd(H, mu):
    n = H.shape[0]
    Re = np.rint(H.real).astype(int); Im = np.rint(H.imag).astype(int)
    assert np.allclose(Re + 1j * Im, H, atol=1e-12)
    A = [[(Fraction(int(Re[i, j])) - (mu if i == j else 0), Fraction(int(Im[i, j]))) for j in range(n)] for i in range(n)]
    pivots = []
    for k in range(n):
        pr, pi_ = A[k][k]; assert pi_ == 0
        if pr <= 0: return False, pivots
        pivots.append(pr)
        for i in range(k + 1, n):
            lr, li = A[i][k][0] / pr, A[i][k][1] / pr          # L_ik
            for j in range(k + 1, n):
                ur, ui = A[k][j]
                A[i][j] = (A[i][j][0] - (lr * ur - li * ui), A[i][j][1] - (lr * ui + li * ur))
    return True, pivots

def exact_hermitian_check(H):
    Re = np.rint(H.real).astype(int); Im = np.rint(H.imag).astype(int)
    return (Re == Re.T).all() and (Im == -Im.T).all()

# ----------------------------------------------------------------------------------------------- stage 2
if 2 in STAGES:
    say("=" * 90); say("STAGE 2: decomposition identity on T_3 (512 tiles, 1024-dim)"); t0 = time.time()
    T3 = tiles_at_level(FR30, 3); n = len(T3)
    own, edges = panel_edges(T3)
    fidx = frame_index(np.array([g for g, _, _ in T3]))
    A = np.zeros((2 * n, 2 * n), complex); deg = np.zeros(n, int)
    for a, b, nv, c, c2 in edges:
        C = clifford_link(T3[a][0], T3[b][0], nv)
        A[2*a:2*a+2, 2*b:2*b+2] += C; A[2*b:2*b+2, 2*a:2*a+2] += C.conj().T; deg[a] += 1; deg[b] += 1
    Hpin = 24 * np.eye(2 * n) - A
    Hfree = np.kron(np.diag(deg), np.eye(2)) - A
    say(f" panels: {len(edges)}; tiles with all 24 faces shared: {(deg == 24).sum()} of {n}; degree range {deg.min()}..{deg.max()}")
    # own edge enumeration over ALL lattice edges of the patch
    allcubes = list(own.keys())
    E = edges_touching(allcubes)
    Hsum = np.zeros_like(A); Hint = np.zeros_like(A); n_int = 0; n_edges = len(E)
    tile_interior = np.ones(n, bool)
    for (k, p), cyc in E.items():
        tiles = [own.get(q) for q in cyc]
        complete = all(t is not None for t in tiles)
        if not complete:
            for t in tiles:
                if t is not None: tile_interior[t] = False
        Hl, labels, sig = h_form(cyc, own, fidx)
        if len(labels) <= 1:
            if complete: n_int += 1
            continue
        for ia, ta in enumerate(labels):
            for ib, tb in enumerate(labels):
                Hsum[2*ta:2*ta+2, 2*tb:2*tb+2] += Hl[2*ia:2*ia+2, 2*ib:2*ib+2] / 4
                if complete: Hint[2*ta:2*ta+2, 2*tb:2*tb+2] += Hl[2*ia:2*ia+2, 2*ib:2*ib+2] / 4
        if complete: n_int += 1
    say(f" lattice edges touching the patch: {n_edges}; with all 4 cubes present (interior): {n_int}")
    d_free = np.abs(Hsum - Hfree).max()
    say(f" (1/4) sum over ALL edges of h_e  vs  free form D - A :   max |diff| = {d_free:.3e}   (each panel lies in exactly 4 edges)")
    # panel multiplicity check: count, for each panel, the number of edges whose cycle contains that face
    cnt = collections.Counter()
    for (k, p), cyc in E.items():
        for s in range(4):
            q1, q2 = cyc[s], cyc[(s + 1) % 4]
            if q1 in own and q2 in own and own[q1] != own[q2]: cnt[frozenset((q1, q2))] += 1
    say(f" every shared panel appears in exactly 4 edge cycles: {set(cnt.values()) == {4}}  (panels counted: {len(cnt)} = {len(edges)})")
    rows = np.repeat(tile_interior, 2)
    say(f" tiles all of whose edges are interior: {tile_interior.sum()}; on those rows (1/4) sum over INTERIOR edges vs pinned 24I-A: max |diff| = {np.abs(Hint[rows] - Hpin[rows]).max():.3e}")
    say(f"   same rows, free form vs pinned: {np.abs(Hfree[rows] - Hpin[rows]).max():.3e}; and all such tiles have deg 24: {(deg[tile_interior] == 24).all()}")
    say(f" Hermitian: {np.abs(Hsum - Hsum.conj().T).max():.1e}; Gaussian-integer entries of 4*Hsum: {np.abs(4*Hsum - np.rint(4*Hsum.real) - 1j*np.rint(4*Hsum.imag)).max():.1e}")
    say(f" stage 2 wall time {time.time()-t0:.1f}s"); flush()

# ----------------------------------------------------------------------------------------------- stage 3
TYPES = None
if 3 in STAGES or 5 in STAGES or 6 in STAGES:
    say("=" * 90); say("STAGE 3: star types, lambda_min(h_e), star sums, exact certificate"); t0 = time.time()
    G4, T4 = gen_poses(4); G5, T5 = gen_poses(5)
    # consistency of own pose generator with the repository tiles_at_level
    T3r = tiles_at_level(FR30, 3); G3, T3_ = gen_poses(3)
    assert all((T3r[i][0] == G3[i]).all() and (T3r[i][1] == T3_[i]).all() for i in range(len(T3r)))
    say(" own vectorised pose generator agrees with tiles_at_level on T_3 (all 512 poses, same order)")
    grid4 = owner_grid(4, G4, T4); grid5 = owner_grid(5, G5, T5)
    types4, c4, i4, _ = star_types(4, G4, T4, grid4)
    types5, c5, i5, (tk5, kl5) = star_types(5, G5, T5, grid5, return_tile_keys=True)
    say(f" T_4: {len(G4)} tiles, complete 1-stars {c4}, incomplete (touch boundary) {i4}, distinct types {len(types4)}")
    say(f" T_5: {len(G5)} tiles, complete 1-stars {c5}, incomplete (touch boundary) {i5}, distinct types {len(types5)}")
    say(f" types(T_4) subset of types(T_5): {set(types4) <= set(types5)}")
    # own closure orbit from a seed in T_4
    seed = next(iter(types4)); orbit = {seed}; frontier = [seed]; rounds = 0
    while frontier:
        rounds += 1; new = []
        for k in frontier:
            for kk in Phi_own(k):
                if kk not in orbit: orbit.add(kk); new.append(kk)
        frontier = new
    say(f" own closure orbit from one T_4 star: {len(orbit)} types after {rounds} rounds; equals types(T_5): {orbit == set(types5)}")
    closed = all(kk in orbit for k in orbit for kk in Phi_own(k))
    say(f" Phi(orbit) subset orbit: {closed}")
    TYPES = sorted(types5, key=lambda k: sorted(k))
    sizes = sorted(len(k) for k in TYPES)
    say(f" star sizes (tiles): min {sizes[0]}, max {sizes[-1]}, histogram {dict(collections.Counter(sizes))}")
    # per type: plaquette forms touching the center
    S_float = {}; S_cert = {}; sigs = {}; nonflat = {}; nplaq = {}
    MU = {}
    type_edge_data = {}
    for k in TYPES:
        poses, center = poses_from_key(k); own = owner_dict(poses)
        fidx = np.array([gidx[key(g)] for g, t in poses])
        ccubes = [tuple(int(x) for x in c) for c in cubes_of_poses(poses[center][0][None], poses[center][1][None])[0]]
        E = edges_touching(ccubes)
        tot = 0.0; cnt = 0; nf = 0; ed = []
        for (kk, p), cyc in E.items():
            assert all(q in own for q in cyc)
            Hl, labels, sig = h_form(cyc, own, fidx)
            if len(labels) <= 1: continue
            cnt += 1
            lam = lam_min(Hl)
            if sig not in sigs: sigs[sig] = (Hl, lam)
            else: assert abs(sigs[sig][1] - lam) < 1e-9
            if lam > 1e-9: nf += 1
            tot += max(lam, 0.0); ed.append((sig, lam, len(labels)))
        S_float[k] = tot; nplaq[k] = cnt; nonflat[k] = nf; type_edge_data[k] = ed
    lamvals = sorted(set(round(v[1], 9) for v in sigs.values()))
    say(f" distinct plaquette signatures (pattern, links): {len(sigs)}; distinct lambda_min values: {lamvals}")
    say(f"   analytic: 2-2cos(pi/8)={2-2*np.cos(np.pi/8):.9f}, 2-sqrt3={2-np.sqrt(3):.9f}, 2-sqrt2={2-np.sqrt(2):.9f}")
    say(f" inter-tile edges touching a tile: {min(nplaq.values())}..{max(nplaq.values())}; non-flat: {min(nonflat.values())}..{max(nonflat.values())}")
    Sv = sorted(S_float.values()); argmin = min(S_float, key=S_float.get)
    say(f" star sums S(type): min {Sv[0]:.9f}, max {Sv[-1]:.9f}, distinct values {len(set(round(v,9) for v in Sv))}")
    say(f" FLOAT bound (1/4) min S = {Sv[0]/4:.9f}  (claim 1.5687255; float >= 1.5687: {Sv[0]/4 >= 1.5687})")
    say(f" argmin type: {len(argmin)} tiles, {nplaq[argmin]} inter-tile edges, {nonflat[argmin]} non-flat; lambda_min multiset: {dict(collections.Counter(round(l,6) for _,l,_ in type_edge_data[argmin]))}")
    say(f" argmin type (relative poses (frame idx, dx,dy,dz)): {[decode(c) for c in sorted(argmin)]}")
    # exact certificate, own LDL^*, for EVERY signature
    nfail = 0; ncert = 0
    for sig, (Hl, lam) in sigs.items():
        assert exact_hermitian_check(Hl)
        if lam <= 1e-9:
            MU[sig] = Fraction(0); continue
        mu = Fraction(int(lam * 10**6) - 2, 10**6)
        ok, piv = exact_pd(Hl, mu)
        if not ok: nfail += 1; say(f"   CERTIFICATE FAILED for {sig}")
        else: ncert += 1
        # also: mu + 1e-5 above lambda_min must FAIL (sanity that the test has teeth)
        ok2, _ = exact_pd(Hl, Fraction(int(lam * 10**6) + 20, 10**6))
        assert not ok2, "exact test accepted a shift above lambda_min"
        MU[sig] = mu
    say(f" own exact LDL^* certificate: {ncert} non-flat signatures certified (h_e - mu_e I positive definite, mu_e = floor(1e6 lambda)-2 over 1e6), {nfail} failures; {sum(1 for s in MU if MU[s]==0)} flat signatures (mu=0)")
    say(f"   sanity: for every non-flat signature the same test REJECTS mu_e + 2.2e-5 (so the pivots detect lambda_min)")
    # flat signatures: check exactly that h_e has a kernel (det = 0 exactly via LDL hitting a zero pivot) -> lambda_min = 0 exactly
    nflat_exact = 0
    for sig, (Hl, lam) in sigs.items():
        if lam <= 1e-9:
            ok, _ = exact_pd(Hl, Fraction(0))
            assert not ok; nflat_exact += 1
    say(f"   flat signatures: exact elimination of h_e finds a non-positive pivot (singular) for all {nflat_exact} -> mu=0 is the best constant")
    for k in TYPES: S_cert[k] = sum(MU[sig] for sig, _, _ in type_edge_data[k])
    cmin = min(S_cert.values())
    say(f" CERTIFIED (own arithmetic): (1/4) min_types sum mu_e = {cmin}/4 = {cmin/4} = {float(cmin)/4:.9f}")
    say(f"   equals claimed 3137451/2000000: {cmin/4 == Fraction(3137451, 2000000)}")
    say(f" stage 3 wall time {time.time()-t0:.1f}s"); flush()

# ----------------------------------------------------------------------------------------------- stage 4
if 4 in STAGES:
    say("=" * 90); say("STAGE 4: completeness attack — complete vertex stars of T_6 (and T_7), rotated/translated copies"); t0 = time.time()
    V72 = set(TYPES)
    G6, T6 = gen_poses(6); grid6 = owner_grid(6, G6, T6)
    say(f" T_6 generated: {len(G6)} tiles, {7*len(G6)} cubes, owner grid 128^3 ({grid6.nbytes/1e6:.0f} MB) ({time.time()-t0:.1f}s)")
    types6, c6, i6, _ = star_types(6, G6, T6, grid6)
    say(f" T_6: complete 1-stars {c6}, incomplete {i6}, distinct types {len(types6)}; subset of the 72: {set(types6) <= V72}; equal: {set(types6) == V72}; new types: {len(set(types6) - V72)}")
    # boundary exclusion check: a star is complete iff all 63 neighbourhood cubes are in the patch; cross-check with
    # a direct criterion: tiles whose cubes are all at Chebyshev distance >= 1 from the complement of the supertile
    N6 = 2 ** 7
    cub6 = cubes_of_poses(G6, T6)
    occ = grid6 >= 0
    # neighbour-complete cubes: all 26 neighbours occupied (or inside the patch)
    pad = np.zeros((N6 + 2,) * 3, bool); pad[1:-1, 1:-1, 1:-1] = occ
    full = np.ones((N6,) * 3, bool)
    for d in itertools.product((0, 1, 2), repeat=3):
        full &= pad[d[0]:d[0]+N6, d[1]:d[1]+N6, d[2]:d[2]+N6]
    tile_ok = full[cub6[..., 0], cub6[..., 1], cub6[..., 2]].all(1)
    say(f" independent boundary criterion (all 26 neighbours of all 7 cubes occupied): {tile_ok.sum()} complete tiles — agrees with {c6}: {tile_ok.sum() == c6}")
    # rotated and translated copies
    rng = np.random.default_rng(7)
    for trial in range(3):
        R = Gs[rng.integers(NG)]; sh = rng.integers(-5, 6, size=3)
        Gr = np.einsum('ij,njk->nik', R, G6.astype(np.int64)).astype(np.int8)
        Tr = (np.einsum('ij,nj->ni', R, T6.astype(np.int64)) + sh).astype(np.int32)
        cub = cubes_of_poses(Gr, Tr); mn = cub.reshape(-1, 3).min(0)
        # shift into a nonnegative grid (translation only changes T; the star keys are translation invariant)
        Tr2 = Tr - mn.astype(np.int32)
        cub = cubes_of_poses(Gr, Tr2); M = int(cub.max()) + 1
        grid = np.full((M, M, M), -1, np.int32); flat = cub.reshape(-1, 3)
        grid[flat[:, 0], flat[:, 1], flat[:, 2]] = np.repeat(np.arange(len(Gr), dtype=np.int32), 7)
        tr, ctr, itr, _ = star_types(6, Gr, Tr2, grid)
        say(f" rotated copy (frame #{gidx[key(R)]}, shift {tuple(int(x) for x in sh)}): complete {ctr}, types {len(tr)}, equal to the 72: {set(tr) == V72}")
        del grid
    del grid6, cub6, occ, pad, full
    # T_7 if memory allows (2,097,152 tiles; grid 256^3 int32 = 67 MB)
    try:
        t1 = time.time()
        G7, T7 = gen_poses(7); grid7 = owner_grid(7, G7, T7)
        types7, c7, i7, _ = star_types(7, G7, T7, grid7, chunk=8192)
        say(f" T_7: {len(G7)} tiles, complete 1-stars {c7}, incomplete {i7}, distinct types {len(types7)}; equal to the 72: {set(types7) == V72}; new: {len(set(types7)-V72)} ({time.time()-t1:.0f}s)")
        del G7, T7, grid7
    except MemoryError as e:
        say(f" T_7 skipped (memory): {e}")
    say(f" stage 4 wall time {time.time()-t0:.1f}s"); flush()

# ----------------------------------------------------------------------------------------------- stage 5
PSI5 = None
if 5 in STAGES:
    say("=" * 90); say("STAGE 5: LOBPCG ground state of pinned T_5 and the slack diagnostic"); t0 = time.time()
    import scipy.sparse as sps, scipy.sparse.linalg as spl
    N = len(G5); f5 = frame_index(G5)
    # sparse pinned H = 24 I - A from the owner grid (own assembly)
    rows = []; cols = []; vals = []
    cub = cubes_of_poses(G5, T5)
    for ax in range(3):
        d = np.zeros(3, int); d[ax] = 1
        nb = lookup(grid5, cub + d)                               # (N,7)
        a = np.repeat(np.arange(N), 7); b = nb.ravel(); m = (b >= 0) & (b != a); a = a[m]; b = b[m]
        C = LINK[f5[a], f5[b], ax]                                # (m,2,2)
        for i in range(2):
            for j in range(2):
                rows.append(2*a+i); cols.append(2*b+j); vals.append(-C[:, i, j])
                rows.append(2*b+j); cols.append(2*a+i); vals.append(-C[:, i, j].conj())
    rows = np.concatenate(rows); cols = np.concatenate(cols); vals = np.concatenate(vals)
    H5 = sps.coo_matrix((vals, (rows, cols)), shape=(2*N, 2*N)).tocsr() + 24 * sps.identity(2*N, format='csr')
    npan = (H5.nnz - 2*N) // 8   # each panel: 2 blocks of 4 entries (no accidental cancellations expected)
    say(f" pinned H on T_5 assembled: dim {2*N}, nnz {H5.nnz}, Hermitian: {abs(H5 - H5.conj().T).max() < 1e-12}")
    rng = np.random.default_rng(1); X = rng.standard_normal((2*N, 4)) + 1j * rng.standard_normal((2*N, 4))
    t1 = time.time()
    w, V = spl.lobpcg(H5, X, largest=False, tol=1e-6, maxiter=3000)
    psi = V[:, np.argmin(w)]; psi = psi / np.linalg.norm(psi)
    Hpsi = H5 @ psi; rq = float(np.vdot(psi, Hpsi).real); res = float(np.linalg.norm(Hpsi - rq * psi))
    say(f" LOBPCG (block 4, tol 1e-6): lowest Ritz values {np.sort(w.real)[:4]}; Rayleigh quotient of best vector {rq:.9f}, residual {res:.2e} ({time.time()-t1:.0f}s)")
    say(f" UPPER BOUND E_bulk <= {rq:.7f}  (<= 8.797: {rq <= 8.797});  Kramers pair gap |w1-w0| = {abs(np.sort(w.real)[1]-np.sort(w.real)[0]):.2e}")
    PSI5 = psi.reshape(N, 2)
    # ---- slack diagnostic over all interior lattice edges of T_5
    N5 = 2 ** 6
    pts = np.array(list(itertools.product(range(N5 + 1), repeat=3)))
    Oall = []; Call = []
    for k in range(3):
        i, j = [x for x in range(3) if x != k]
        cyc = []
        for a, b in CYC:
            q = pts.copy(); q[:, i] -= a; q[:, j] -= b; cyc.append(q)
        cyc = np.stack(cyc, 1)                                    # (P,4,3)
        O = lookup(grid5, cyc)
        m = (O >= 0).all(1)
        Oall.append(O[m]); Call.append(cyc[m])
    O = np.concatenate(Oall); CY = np.concatenate(Call); ne = len(O)
    say(f" interior lattice edges of T_5 (all 4 cubes present): {ne}")
    # face terms and h_e(psi)
    he = np.zeros(ne); lab = np.full((ne, 4), 8, int)
    for s in range(4):
        a = O[:, s]; b = O[:, (s + 1) % 4]
        d = CY[:, (s + 1) % 4] - CY[:, s]; ax = np.nonzero(d)[1]
        m = a != b
        C = LINK[f5[a[m]], f5[b[m]], ax[m]]
        diff = PSI5[a[m]] - np.einsum('nij,nj->ni', C, PSI5[b[m]])
        he[m] += (np.abs(diff) ** 2).sum(1)
        lab[m, s] = LINKLAB[f5[a[m]], f5[b[m]], ax[m]]
    # pattern code
    pat = np.zeros((ne, 4), int)
    for s in range(4):
        first = np.full(ne, s)
        for r in range(s - 1, -1, -1):
            first = np.where(O[:, r] == O[:, s], r, first)
        pat[:, s] = first
    code = ((((pat[:, 0]*4 + pat[:, 1])*4 + pat[:, 2])*4 + pat[:, 3])*10**4 + ((lab[:, 0]*10 + lab[:, 1])*10 + lab[:, 2])*10 + lab[:, 3])
    uc, first, inv = np.unique(code, return_index=True, return_inverse=True)
    lam_u = np.zeros(len(uc))
    own5 = {}
    for r, e in enumerate(first):
        cyc = [tuple(int(x) for x in q) for q in CY[e]]
        own_loc = {q: int(O[e, s]) for s, q in enumerate(cyc)}
        Hl, labels, sig = h_form(cyc, own_loc, f5)
        lam_u[r] = lam_min(Hl) if len(labels) > 1 else 0.0
    lam_e = lam_u[inv.ravel()]
    say(f" distinct interior edge signatures in T_5 (incl. boundary-adjacent ones, labelled by first-occurrence pattern): {len(uc)}; inter-tile edges: {(pat != 0).any(1).sum()}, single-tile edges: {(pat == 0).all(1).sum()}")
    # norms of psi on V(e)
    w2 = (np.abs(PSI5) ** 2).sum(1)
    firstocc = np.ones((ne, 4), bool)
    for s in range(4):
        for r in range(s):
            firstocc[:, s] &= O[:, r] != O[:, s]
    normV = (w2[O] * firstocc).sum(1)
    E_int = he.sum() / 4; LB_int = (lam_e * normV).sum() / 4
    say(f" (1/4) sum_e h_e(psi) over interior edges = {E_int:.6f}; remaining (boundary faces + pinning) = {rq - E_int:.6f}")
    say(f" (1/4) sum_e lambda_min(h_e) ||psi_V(e)||^2 = {LB_int:.6f}  -> loss factor from h_e >= lambda_min P_V(e): {E_int/LB_int:.3f}")
    # star-type weighted sum of S: equals LB_int restricted to complete-star tiles
    Sarr = np.zeros(N); comp = tk5 >= 0
    S_by_key = {k: S_float[k] for k in TYPES}
    for i in np.nonzero(comp)[0]: Sarr[i] = S_by_key[kl5[tk5[i]]]
    wS = (Sarr[comp] * w2[comp]).sum() / 4
    say(f" psi-weighted star bound (1/4) sum_a S(a)|psi_a|^2 over complete-star tiles = {wS:.6f} (mass on complete-star tiles {w2[comp].sum():.4f}); min S/4 = {Sv[0]/4:.6f}")
    say(f"   gap decomposition: 8.797 = E_int + boundary;  E_int / LB_int = {E_int/LB_int:.3f} (cross-plaquette correlations discarded);  LB_int vs min-type bound: {LB_int/(Sv[0]/4):.3f} (weak stars carry little psi mass)")
    # per-type ratio
    num = np.zeros(N); den = np.zeros(N)
    for s in range(4):
        m = firstocc[:, s]
        np.add.at(num, O[m, s], he[m]); np.add.at(den, O[m, s], lam_e[m] * normV[m])
    ratio_by_type = collections.defaultdict(lambda: [0.0, 0.0, 0.0])
    for i in np.nonzero(comp)[0]:
        r = ratio_by_type[kl5[tk5[i]]]; r[0] += num[i]; r[1] += den[i]; r[2] += w2[i]
    say(" per star type (sorted by S): S(type)/4, psi-mass fraction, ratio [sum_e h_e(psi)] / [sum_e lambda_min ||psi_V||^2] over tiles of that type")
    for k in sorted(TYPES, key=S_float.get):
        r = ratio_by_type.get(k)
        if r is None: say(f"   S/4={S_float[k]/4:7.4f}  (type absent among complete stars of T_5)"); continue
        say(f"   S/4={S_float[k]/4:7.4f}  mass={r[2]:.5f}  ratio={r[0]/r[1] if r[1]>0 else float('nan'):7.3f}  |star|={len(k)}")
    say(f" stage 5 wall time {time.time()-t0:.1f}s"); flush()

# ----------------------------------------------------------------------------------------------- stage 6
if 6 in STAGES:
    say("=" * 90); say("STAGE 6: cheap improvements (FLOAT ONLY, UNCERTIFIED)"); t0 = time.time()
    # (a) vertex-block decomposition: <psi,Hpsi> = sum_v k_v(psi), k_v = (1/4) * (form of the 12 faces of the 2x2x2 block at v)
    #     bound: E >= min_type sum_{v vertex of center} lambda_min(k_v), needs only the 72 types.
    S_vert = {}; S_vert_cert = {}; vsigs = {}
    for k in TYPES:
        poses, center = poses_from_key(k); own = owner_dict(poses)
        fidx = np.array([gidx[key(g)] for g, t in poses])
        ccubes = [tuple(int(x) for x in c) for c in cubes_of_poses(poses[center][0][None], poses[center][1][None])[0]]
        verts = set()
        for c in ccubes:
            for d in itertools.product((0, 1), repeat=3): verts.add((c[0]+d[0], c[1]+d[1], c[2]+d[2]))
        assert len(verts) == 26
        tot = 0.0; totc = []
        for v in verts:
            block = [(v[0]-a, v[1]-b, v[2]-c) for a, b, c in itertools.product((0, 1), repeat=3)]
            assert all(q in own for q in block)
            Hb, tiles = block_form(block, own, fidx)
            if len(tiles) > 1:
                lam = lam_min(Hb); tot += max(lam, 0.0) / 4
                # signature for the exact certificate cache: owner labels of the 8 cubes (first occurrence) + frames
                lab = []; seen = {}
                for q in block:
                    t = own[q]; seen.setdefault(t, len(seen)); lab.append((seen[t], int(fidx[t])))
                vs = tuple(lab)
                if vs not in vsigs: vsigs[vs] = (Hb, lam)
                else: assert abs(vsigs[vs][1] - lam) < 1e-9
                totc.append(vs)
        S_vert[k] = tot; S_vert_cert[k] = totc
    vmin = min(S_vert.values())
    say(f" (a) vertex-block (2x2x2, weight 1/4) decomposition, 72 types: E_bulk >= min_type sum_v lambda_min(k_v) = {vmin:.6f}  (edge version: {Sv[0]/4:.6f})")
    # exact certificate of (a) with the same rational LDL^* machinery (blocks have <= 8 tiles -> <= 16x16 Gaussian-integer matrices)
    t1 = time.time(); MUV = {}; nfail = 0
    for vs, (Hb, lam) in vsigs.items():
        assert exact_hermitian_check(Hb)
        if lam <= 1e-9:
            ok, _ = exact_pd(Hb, Fraction(0)); assert not ok; MUV[vs] = Fraction(0); continue
        mu = Fraction(int(lam * 10**6) - 2, 10**6)
        ok, _ = exact_pd(Hb, mu)
        if not ok: nfail += 1; say(f"   vertex-block certificate FAILED for {vs}")
        MUV[vs] = mu if ok else Fraction(0)
    vcert = min(sum(MUV[vs] for vs in S_vert_cert[k]) for k in TYPES) / 4
    say(f"     distinct vertex-block signatures: {len(vsigs)} (non-flat {sum(1 for v in vsigs.values() if v[1] > 1e-9)}, max dim {max(v[0].shape[0] for v in vsigs.values())}); exact LDL^* failures: {nfail}")
    say(f"     CERTIFIED (own exact arithmetic, same closure/completeness hypotheses as the 72-type argument): E_bulk >= {vcert} = {float(vcert):.9f}  ({time.time()-t1:.1f}s)")
    # convex mixing: H = t*(edge decomposition) + (1-t)*(vertex decomposition), bound min_type [t*S_e/4 + (1-t)*S_v]
    best = (0, -1)
    for t in np.linspace(0, 1, 1001):
        val = min(t * S_float[k] / 4 + (1 - t) * S_vert[k] for k in TYPES)
        if val > best[1]: best = (t, val)
    say(f"     convex mixing edge/vertex decompositions: best t={best[0]:.3f}, bound {best[1]:.6f}")
    # (b) cube-centred 3x3x3 blocks, weight 1/18 (each face lies in exactly 18 such blocks); needs 2-stars.
    #     E >= min_a (1/18) sum_{c in nbhd(a)} lambda_min(B_c): evaluated on tiles of T_5 with complete 2-stars.
    t1 = time.time()
    N = len(G5); f5 = frame_index(G5)
    types2_5, c2_5, i2_5, (tk2, kl2) = star_types(5, G5, T5, grid5, odd=L2ODD, return_tile_keys=True)
    say(f" (b) 2-stars (Chebyshev radius 2, 215 positions) of T_5: complete {c2_5}, distinct types {len(types2_5)}")
    # lambda_min(B_c) for every cube c of T_5 whose 3-block is inside the patch, cached by block signature
    cub = cubes_of_poses(G5, T5).reshape(-1, 3)
    N5 = 2 ** 6
    offs = np.array(list(itertools.product((-1, 0, 1), repeat=3)))
    blk = cub[:, None, :] + offs[None]                           # (7N,27,3)
    Ob = lookup(grid5, blk); okb = (Ob >= 0).all(1)
    # signature: relative frames and relative positions are fixed by the block geometry given the owner pattern
    # + frames; use (owner-pattern labels in order of first appearance, frame index of each cube's tile)
    fcube = np.where(okb[:, None], f5[np.where(Ob >= 0, Ob, 0)], -1)
    patb = np.zeros_like(Ob)
    for s in range(27):
        first = np.full(len(Ob), s)
        for r in range(s - 1, -1, -1):
            first = np.where(Ob[:, r] == Ob[:, s], r, first)
        patb[:, s] = first
    sigrows = np.concatenate([patb, fcube], 1)[okb]
    ub, firstb, invb = np.unique(sigrows, axis=0, return_index=True, return_inverse=True)
    say(f"     cubes with full 3-block inside T_5: {okb.sum()} of {len(cub)}; distinct 3-block signatures: {len(ub)}")
    lamb_u = np.zeros(len(ub)); idx_ok = np.nonzero(okb)[0]
    for r, e in enumerate(firstb):
        c0 = idx_ok[e]
        block = [tuple(int(x) for x in q) for q in blk[c0]]
        own_loc = {q: int(Ob[c0, s]) for s, q in enumerate(block)}
        Hb, tiles = block_form(block, own_loc, f5)
        lamb_u[r] = lam_min(Hb) if len(tiles) > 1 else 0.0
    lam_cube = np.full(len(cub), np.nan); lam_cube[okb] = lamb_u[invb.ravel()]
    say(f"     distinct lambda_min(B_c) values: {len(set(np.round(lamb_u, 9)))}, min {lamb_u.min():.6f}, max {lamb_u.max():.6f} ({time.time()-t1:.0f}s)")
    # per tile with complete 2-star: sum over the 63 neighbourhood cubes c (blocks meeting the tile) of lambda_min(B_c)/18
    P63 = cubes_of_poses(G5, T5, L1ODD)                           # (N,63,3)
    flatidx = P63[..., 0] * N5 * N5 + P63[..., 1] * N5 + P63[..., 2]
    cubeflat = cub[:, 0] * N5 * N5 + cub[:, 1] * N5 + cub[:, 2]
    lam_grid = np.full(N5 ** 3, np.nan); lam_grid[cubeflat] = lam_cube
    inside = ((P63 >= 0) & (P63 < N5)).all(-1)
    vals = np.where(inside, lam_grid[np.where(inside, flatidx, 0)], np.nan)
    comp2 = tk2 >= 0
    S3 = np.nansum(vals, 1) / 18
    good = comp2 & ~np.isnan(vals).any(1)
    say(f"     tiles with complete 2-star and all 63 blocks defined: {good.sum()}")
    S3min = S3[good].min()
    say(f"     3-block (weight 1/18) decomposition evaluated on T_5 2-star types: E_bulk >= {S3min:.6f}   [UNCERTIFIED: completeness of 2-star types not established here]")
    # also: edge bound and vertex-block bound restricted to the same tiles, for comparison, plus the best mix of the three
    say(f"     for comparison on the same tiles: edge bound {min(S_float[kl5[tk5[i]]]/4 for i in np.nonzero(good)[0]):.6f}, vertex-block bound {min(S_vert[kl5[tk5[i]]] for i in np.nonzero(good)[0]):.6f}")
    bestmix = (None, -1)
    Se = np.array([S_float[kl5[tk5[i]]]/4 for i in np.nonzero(good)[0]]); Svv = np.array([S_vert[kl5[tk5[i]]] for i in np.nonzero(good)[0]]); S3g = S3[good]
    for t1_ in np.linspace(0, 1, 101):
        for t2_ in np.linspace(0, 1 - t1_, int(round((1 - t1_) * 100)) + 1):
            val = (t1_ * Se + t2_ * Svv + (1 - t1_ - t2_) * S3g).min()
            if val > bestmix[1]: bestmix = ((t1_, t2_, 1 - t1_ - t2_), val)
    say(f"     best convex mix (edge, vertex, 3-block) weights {tuple(round(x,2) for x in bestmix[0])}: {bestmix[1]:.6f}  [UNCERTIFIED]")
    # 2-star type count on T_6 as a completeness heuristic for (b)
    try:
        t2 = time.time()
        G6, T6 = gen_poses(6); grid6 = owner_grid(6, G6, T6)
        types2_6, c2_6, _, _ = star_types(6, G6, T6, grid6, odd=L2ODD, chunk=8192)
        say(f"     2-star types in T_6: {len(types2_6)} (complete {c2_6}); T_5 types subset: {set(types2_5) <= set(types2_6)}; new in T_6: {len(set(types2_6) - set(types2_5))} ({time.time()-t2:.0f}s)")
        del G6, T6, grid6
    except MemoryError as e:
        say(f"     2-star T_6 count skipped: {e}")
    say(f" stage 6 wall time {time.time()-t0:.1f}s"); flush()

say("=" * 90); say(f"total wall time {time.time()-T_START:.1f}s"); flush()
