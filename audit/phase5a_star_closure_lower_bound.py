"""
Phase 5a / Task B3: a RIGOROUS POSITIVE LOWER BOUND on E_bulk = inf spec(H_omega) via a local decomposition.

Decomposition.  In every tiling omega of the hull every lattice edge e is surrounded by 4 unit cubes.  Let h_e be the
quadratic form of the 4-cycle of tiles around e (terms |psi_a - C_f psi_b|^2 for the faces f containing e that are
panels, i.e. separate different tiles).  Each panel contains 4 lattice edges, hence
        <psi, H_omega psi> = sum_f |psi_a - C_f psi_b|^2 = (1/4) sum_e h_e(psi).
Since h_e >= lambda_min(h_e) P_{V(e)} (V(e) = tiles meeting e), we get
        H_omega >= (1/4) sum_a S(a) P_a,   S(a) = sum_{e touching a} lambda_min(h_e),
so  E_bulk >= (1/4) inf_a S(a).  S(a) depends only on the VERTEX-STAR type of a (the tile a together with all tiles
sharing at least a vertex with it, with frames, up to rigid motion).

Closure.  The vertex-star of a child of a tile A is contained in the inflation of the vertex-star of A (parents of
26-adjacent fine cubes are 26-adjacent or equal).  Hence the collared substitution Phi (star of A -> stars of the 8
children of A) is well defined on legal stars, and by repetitivity of the hull (PHASE5A_INFINITE_VOLUME_FRAMEWORK.md,
Theorem 1.9) the set of ALL legal vertex-star types equals the forward Phi-orbit of ANY single legal star.  This
script computes that orbit from one interior tile of T_3, checks it against the complete stars of T_3..T_5, and then
certifies lambda_min(h_e) >= mu_e EXACTLY (rational LDL^* pivots of h_e - mu_e) for every plaquette signature.

Run from the repository root:  python3 -u -I audit/phase5a_star_closure_lower_bound.py
"""
import os, sys, itertools, collections, time
from fractions import Fraction
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
from independent_clifford_q8_audit import FR30, U3, perm_mat, tiles_at_level, clifford_link, q8label

OUT = []
def say(*a):
    s = " ".join(str(x) for x in a); print(s, flush=True); OUT.append(s)
def key(G): return tuple(int(x) for x in np.asarray(G).ravel())

ops = [(perm_mat(FR30['0']), np.array([1, 1, 1]))]
for v in U3:
    ops.append((np.diag([1 - 2 * v[0], 1 - 2 * v[1], 1 - 2 * v[2]]) @ perm_mat(FR30[v]), 4 * np.array(v)))
BASE = [np.array([2 * u[0] + 1, 2 * u[1] + 1, 2 * u[2] + 1]) for u in U3]
NB26 = [d for d in itertools.product((-1, 0, 1), repeat=3) if d != (0, 0, 0)]
I3 = np.eye(3, dtype=int)

def cubes_of(G, T): return frozenset(tuple(int(x) for x in (G @ bc + 2 * T - 1) // 2) for bc in BASE)
def make_patch(poses): return [(G, T, cubes_of(G, T)) for G, T in poses]
def owner_map(patch): return {c: a for a, (_, _, cs) in enumerate(patch) for c in cs}
def inflate(poses): return [(G @ g, 2 * T + G @ t) for G, T in poses for g, t in ops]

def star_members(center, patch, owner):
    cs = patch[center][2]
    need = {(c[0] + d[0], c[1] + d[1], c[2] + d[2]) for c in cs for d in NB26} | set(cs)
    mem = set()
    for c in need:
        if c not in owner: return None
        mem.add(owner[c])
    return mem

def canon(center, members, patch):
    G0, T0, _ = patch[center]
    rel = []
    for b in members:
        Gb, Tb, _ = patch[b]
        rel.append((key(G0.T @ Gb), tuple(int(x) for x in G0.T @ (Tb - T0))))
    return tuple(sorted(rel))

def patch_from_type(typ):
    poses = [(np.array(R).reshape(3, 3), np.array(t)) for R, t in typ]
    patch = make_patch(poses)
    center = [i for i, (R, t) in enumerate(typ) if R == key(I3) and t == (0, 0, 0)]
    assert len(center) == 1
    return patch, center[0]

def Phi(typ):
    """types of the vertex-stars of the 8 children of the center of a legal star."""
    patch, center = patch_from_type(typ)
    G0, T0, _ = patch[center]
    fine = make_patch(inflate([(G, T) for G, T, _ in patch]))
    owner = owner_map(fine)
    out = []
    for c in range(8):
        idx = 8 * center + c
        mem = star_members(idx, fine, owner)
        assert mem is not None, "child star not complete inside inflated parent star: closure argument fails"
        out.append(canon(idx, mem, fine))
    return out

# ---------------------------------------------------------------- 1. forward orbit of one legal star
say("=" * 78); say("1. LEGAL VERTEX-STAR TYPES = FORWARD ORBIT OF ONE LEGAL STAR UNDER THE COLLARED SUBSTITUTION")
t0 = time.time()
T3 = tiles_at_level(FR30, 3); own3 = owner_map(T3)
complete3 = {a: star_members(a, T3, own3) for a in range(len(T3))}
complete3 = {a: m for a, m in complete3.items() if m is not None}
seed_tile = min(complete3)
seed = canon(seed_tile, complete3[seed_tile], T3)
say(f" seed: interior tile {seed_tile} of T_3, vertex-star has {len(seed)} tiles")
types = {seed}; frontier = [seed]; rounds = 0
while frontier:
    rounds += 1; new = []
    for typ in frontier:
        for ch in Phi(typ):
            if ch not in types: types.add(ch); new.append(ch)
    say(f"   round {rounds}: {len(new)} new types, total {len(types)}")
    frontier = new
V = types
say(f" |V| = {len(V)} legal vertex-star types (sizes {min(len(t) for t in V)}..{max(len(t) for t in V)} tiles)  ({time.time()-t0:.0f}s)")
# closure and consistency checks
closed = all(ch in V for typ in V for ch in Phi(typ))
say(f" Phi(V) subset V (closure): {closed}")
for m in (3, 4, 5):
    t1 = time.time(); Tm = tiles_at_level(FR30, m); own = owner_map(Tm)
    Sm = set()
    for a in range(len(Tm)):
        mem = star_members(a, Tm, own)
        if mem is not None: Sm.add(canon(a, mem, Tm))
    say(f" complete vertex-stars of T_{m}: {len(Sm)} types; all in V: {Sm <= V}; V \\ S_{m}: {len(V - Sm)}  ({time.time()-t1:.0f}s)")
# second seed for robustness
seed2_tile = max(complete3); seed2 = canon(seed2_tile, complete3[seed2_tile], T3)
types2 = {seed2}; fr = [seed2]
while fr:
    new = []
    for typ in fr:
        for ch in Phi(typ):
            if ch not in types2: types2.add(ch); new.append(ch)
    fr = new
say(f" forward orbit from a second seed (tile {seed2_tile}): {len(types2)} types; equal to V: {types2 == V}")

# ---------------------------------------------------------------- 2. plaquette forms and per-type S
say("=" * 78); say("2. PLAQUETTE FORMS h_e, lambda_min, AND S(type) = sum over edges touching the center")
def plaquettes_touching_center(patch, center, owner):
    """lattice edges touching the center tile; returns list of (4 cubes in cyclic order)."""
    cs = patch[center][2]; seen = set(); out = []
    for c in cs:
        for k in range(3):
            i, j = [x for x in range(3) if x != k]
            for di, dj in itertools.product((0, 1), repeat=2):
                p = list(c); p[i] += di; p[j] += dj; p = tuple(p)        # lattice point: edge from p to p+e_k
                ek = (k, p)
                if ek in seen: continue
                seen.add(ek)
                def shift(q, a, b):
                    q = list(q); q[i] -= a; q[j] -= b; return tuple(q)
                cyc = [shift(p, 0, 0), shift(p, 1, 0), shift(p, 1, 1), shift(p, 0, 1)]
                assert all(q in owner for q in cyc)
                out.append(cyc)
    return out

def h_matrix(cyc, patch, owner):
    tiles = [owner[q] for q in cyc]
    labels = sorted(set(tiles)); loc = {t: i for i, t in enumerate(labels)}
    n = len(labels); H = np.zeros((2 * n, 2 * n), complex); sig_links = []
    for s in range(4):
        q1, q2 = cyc[s], cyc[(s + 1) % 4]; t1, t2 = owner[q1], owner[q2]
        if t1 == t2: sig_links.append('same'); continue
        nvec = np.array(q2) - np.array(q1)
        C = clifford_link(patch[t1][0], patch[t2][0], nvec)
        a, b = loc[t1], loc[t2]
        H[2*a:2*a+2, 2*a:2*a+2] += np.eye(2); H[2*b:2*b+2, 2*b:2*b+2] += np.eye(2)
        H[2*a:2*a+2, 2*b:2*b+2] -= C; H[2*b:2*b+2, 2*a:2*a+2] -= C.conj().T
        sig_links.append(q8label(C))
    pattern = tuple(loc[t] for t in tiles)
    return H, (pattern, tuple(sig_links)), n

lam_cache = {}; mat_cache = {}
S = {}; nplaq = {}; nnonflat = {}
for typ in V:
    patch, center = patch_from_type(typ); owner = owner_map(patch)
    tot = 0.0; cnt = 0; nf = 0
    for cyc in plaquettes_touching_center(patch, center, owner):
        H, sig, n = h_matrix(cyc, patch, owner)
        if n == 1: continue                       # all four cubes in the center tile: h_e = 0
        cnt += 1
        if sig not in lam_cache:
            lam_cache[sig] = float(np.linalg.eigvalsh(H)[0]); mat_cache[sig] = H
        lam = lam_cache[sig]
        if lam > 1e-9: nf += 1
        tot += max(lam, 0.0)
    S[typ] = tot; nplaq[typ] = cnt; nnonflat[typ] = nf
say(f" distinct plaquette signatures (pattern, links): {len(lam_cache)}")
lam_vals = sorted(set(round(v, 9) for v in lam_cache.values()))
say(f" distinct lambda_min(h_e) values: {lam_vals}")
say(" analytic check: simple l-cycle with holonomy angle theta has lambda_min = 2-2cos(theta/l):",
    f" l=4,theta=pi: {2-2*np.cos(np.pi/4):.6f}; l=4,theta=pi/2: {2-2*np.cos(np.pi/8):.6f}; l=3,theta=pi: {2-2*np.cos(np.pi/3):.6f}; l=3,theta=pi/2: {2-2*np.cos(np.pi/6):.6f}; l=2,theta=pi: {2-2*np.cos(np.pi/2):.6f}; l=2,theta=pi/2: {2-2*np.cos(np.pi/4):.6f}")
Svals = sorted(S.values())
say(f" S(type): min {Svals[0]:.6f}, median {Svals[len(Svals)//2]:.6f}, max {Svals[-1]:.6f}")
say(f" inter-tile plaquettes touching a tile: {min(nplaq.values())}..{max(nplaq.values())}; non-flat among them: {min(nnonflat.values())}..{max(nnonflat.values())}")
worst = min(S, key=S.get)
say(f" weakest type: {len(worst)} tiles in star, {nplaq[worst]} inter-tile plaquettes, {nnonflat[worst]} non-flat, S = {S[worst]:.6f}")
say(f" FLOAT lower bound: E_bulk >= (1/4) min S = {Svals[0]/4:.6f}")

# ---------------------------------------------------------------- 3. exact certification
say("=" * 78); say("3. EXACT CERTIFICATION lambda_min(h_e) >= mu_e BY RATIONAL LDL^* PIVOTS")
def gauss_entries(H):
    M = np.rint(np.stack([H.real, H.imag], -1)).astype(int)
    assert np.allclose(M[..., 0] + 1j * M[..., 1], H, atol=1e-12)
    return M
def is_pd_exact(H, mu):
    """H Hermitian with Gaussian-integer entries; test H - mu*I positive definite via exact elimination."""
    M = gauss_entries(H); n = H.shape[0]
    A = [[(Fraction(int(M[i, j, 0])) - (mu if i == j else 0), Fraction(int(M[i, j, 1]))) for j in range(n)] for i in range(n)]
    for k in range(n):
        pr, pi = A[k][k]
        assert pi == 0
        if pr <= 0: return False
        for i in range(k + 1, n):
            lr, li = A[i][k]            # L_ik = A_ik / pivot
            lr, li = lr / pr, li / pr
            for j in range(k + 1, n):
                ur, ui = A[k][j]
                # A_ij -= L_ik * A_kj
                A[i][j] = (A[i][j][0] - (lr * ur - li * ui), A[i][j][1] - (lr * ui + li * ur))
    return True
mu = {}
for sig, lam in lam_cache.items():
    if lam <= 1e-9: mu[sig] = Fraction(0); continue
    m_ = Fraction(int(lam * 10**6) - 2, 10**6)
    ok = is_pd_exact(mat_cache[sig], m_)
    assert ok, f"certification failed for {sig}"
    mu[sig] = m_
say(f" certified {sum(1 for s in mu if mu[s] > 0)} non-flat signatures (mu_e = lambda_min - 2e-6 rounded), {sum(1 for s in mu if mu[s] == 0)} flat signatures assigned 0")
Scert = {}
for typ in V:
    patch, center = patch_from_type(typ); owner = owner_map(patch); tot = Fraction(0)
    for cyc in plaquettes_touching_center(patch, center, owner):
        H, sig, n = h_matrix(cyc, patch, owner)
        if n == 1: continue
        tot += mu[sig]
    Scert[typ] = tot
cmin = min(Scert.values())
say(f" CERTIFIED: E_bulk >= (1/4) min_types sum_e mu_e = {cmin}/4 = {float(cmin)/4:.6f}")
say(f" sanity: every legal star has at least one non-flat plaquette: {min(nnonflat.values()) >= 1}")
with open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'results', 'phase5a_star_closure_lower_bound.txt'), 'w') as f:
    f.write("\n".join(OUT) + "\n")
