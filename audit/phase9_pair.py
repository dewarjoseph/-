#!/usr/bin/env python3
"""Phase IX, Part III: the rule pair 937/938, rebuilt from deliverables/PHASE7_DEFINITIONS.md.

Independent of the census code (phase5b_*), except that the index -> decoration map is re-derived here and cross-checked.
Tiles, panels, links (Pauli formula U_f(a->b) = (sigma.M_a^T n)(sigma.M_b^T n)), plaquettes (4-cycles of cubes around a lattice
edge) and the pinned operator H = 24 - A_U are computed from the definitions.  A decoration can be chosen per substitution
step ("step-resolved rules"): step 1 creates the depth-1 children of the root, step L the individual tiles.  The link across a
seam between subtrees that separate at depth k depends only on the choices at steps k..L (the parent frames above cancel).

Subcommands (each writes audit/results/phase9_<cmd>.json):
  pair      reproduction: index map, S3-orbits, geometry identity, class counts and class fields, two-cycles, Y_L (L = 3..5),
            certified level-3 enclosures (exact Rayleigh quotient above, Higham-certified Cholesky below)
  moments   exact spectral moments tr(A^p), p <= 12, at level 3 for 937, 938; first differing order; where it differs
  steps     step-resolved rules: Y_L for every centre-choice sequence in {937, 938}^L (L = 3, 4, 5), class counts, main effects
  ladder    patch-scale ladder U_m (m = 0..3) over the legal 1-star types of 937, 938, FR30; ladder01: m = 0, 1 only
  edge, cert4, loops  comparison columns; level-4 certificates; fourth-moment decomposition
Usage: python -u -I audit/phase9_pair.py <cmd> [<cmd> ...]"""
import os, sys, json, time, math, itertools, collections, types
from fractions import Fraction
sys.modules.setdefault('resource', types.SimpleNamespace(getrusage=lambda *a: types.SimpleNamespace(ru_maxrss=0), RUSAGE_SELF=0))
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); RES = os.path.join(HERE, 'results')
import numpy as np, scipy.sparse as sps, scipy.sparse.linalg as sla
T0 = time.time()
def log(*a): print(f"[{time.time()-T0:7.0f}s]", *a, flush=True)
def save(name, obj): json.dump(obj, open(os.path.join(RES, f'phase9_{name}.json'), 'w'), indent=1, default=float)

# ------------------------------------------------------------------ decorations (definitions section 1)
U3 = [v for v in itertools.product((0, 1), repeat=3) if v != (1, 1, 1)]
def psign(p): return int(round(np.linalg.det(np.eye(3)[list(p)])))
PERMS = list(itertools.permutations(range(3)))
EVEN = [p for p in PERMS if psign(p) == 1]; ODD = [p for p in PERMS if psign(p) == -1]
def decoration(i):
    """census index -> decoration: base-3 digits, digit 0 = centre child (EVEN), digit k = octant U3[k-1] (EVEN/ODD by parity)"""
    d = [(i // 3 ** k) % 3 for k in range(8)]
    dec = {'0': EVEN[d[0]]}
    for k, v in enumerate(U3): dec[v] = (EVEN if sum(v) % 2 == 0 else ODD)[d[k + 1]]
    return dec
def pmat(p):
    M = np.zeros((3, 3), dtype=np.int64)
    for i in range(3): M[i, p[i]] = 1
    return M
def ops(dec):
    out = [(pmat(dec['0']), np.array([1, 1, 1]))]
    for v in U3: out.append((np.diag([1 - 2 * x for x in v]) @ pmat(dec[v]), 4 * np.array(v)))
    return out

def poses(decs):
    """decs[j] is the decoration used at substitution step j+1 (step 1 = root -> depth-1 children)"""
    G = np.eye(3, dtype=np.int64)[None]; T = np.zeros((1, 3), dtype=np.int64)
    for dec in decs:
        o = ops(dec); g = np.stack([x for x, _ in o]); t = np.stack([y for _, y in o])
        T = (2 * T[:, None, :] + np.einsum('nij,cj->nci', G, t)).reshape(-1, 3); G = np.einsum('nij,cjk->ncik', G, g).reshape(-1, 3, 3)
    return G, T
BASE = np.array([[2 * u[0] + 1, 2 * u[1] + 1, 2 * u[2] + 1] for u in U3])
def owner_grid(G, T, L):
    N = 2 ** (L + 1); grid = -np.ones((N, N, N), dtype=np.int64)
    C = (np.einsum('nij,uj->nui', G, BASE) + 2 * T[:, None, :] - 1) // 2
    assert (grid[C[..., 0], C[..., 1], C[..., 2]] == -1).all()
    grid[C[..., 0], C[..., 1], C[..., 2]] = np.arange(len(G))[:, None]
    assert ((grid >= 0).sum() == 7 * len(G))
    return grid

# ------------------------------------------------------------------ links (definitions section 3)
SIG = np.array([[[0, 1], [1, 0]], [[0, -1j], [1j, 0]], [[1, 0], [0, -1]]], dtype=complex)
def pauli_of(M, ax):
    """sigma . (M^T e_ax) = s * sigma_k for the signed unit vector M^T e_ax = row ax of M"""
    row = M[..., ax, :]; k = np.abs(row).argmax(-1); s = np.take_along_axis(row, k[..., None], -1)[..., 0]
    return k, s
def links(G, a, b, ax):
    ka, sa = pauli_of(G[a], ax) if np.ndim(ax) == 0 else pauli_of_rows(G[a], ax)
    kb, sb = pauli_of(G[b], ax) if np.ndim(ax) == 0 else pauli_of_rows(G[b], ax)
    return (sa * sb)[:, None, None] * np.einsum('nij,njk->nik', SIG[ka], SIG[kb])
def pauli_of_rows(M, ax):
    row = M[np.arange(len(M)), ax, :]; k = np.abs(row).argmax(-1); s = row[np.arange(len(M)), k]
    return k, s

def panels(grid):
    out = []
    for ax in range(3):
        A = np.moveaxis(grid, ax, 0); a = A[:-1].ravel(); b = A[1:].ravel(); m = (a >= 0) & (b >= 0) & (a != b)
        out.append((a[m], b[m], np.full(m.sum(), ax)))
    return tuple(np.concatenate(x) for x in zip(*out))

def operator(G, a, b, ax, n):
    U = links(G, a, b, ax)                                                       # U(a -> b), 2x2
    r = np.concatenate([2 * a[:, None] + np.array([0, 0, 1, 1]), 2 * b[:, None] + np.array([0, 0, 1, 1])]).ravel()
    c = np.concatenate([2 * b[:, None] + np.array([0, 1, 0, 1]), 2 * a[:, None] + np.array([0, 1, 0, 1])]).ravel()
    v = np.concatenate([U.reshape(-1, 4), np.conj(np.transpose(U, (0, 2, 1))).reshape(-1, 4)]).ravel()
    A = sps.csr_matrix((v, (r, c)), shape=(2 * n, 2 * n))
    return (24 * sps.identity(2 * n, format='csr') - A).tocsr()

def build(decs, ref=None):
    """the pinned level-L supertile; with ref (an owner grid), tiles are relabelled to ref's order, which is possible because
    the set of chairs does not depend on the decoration (asserted: the two partitions of the cubes coincide)"""
    L = len(decs); G, T = poses(decs); grid = owner_grid(G, T, L)
    if ref is not None:
        m = ref >= 0; order = np.full(len(G), -1); order[ref[m]] = grid[m]                 # ref tile i <- our tile order[i]
        assert (order >= 0).all() and np.array_equal(order[ref[m]], grid[m]) and len(set(order.tolist())) == len(G)
        G, T = G[order], T[order]; grid = ref.copy()
    a, b, ax = panels(grid)
    return {'L': L, 'G': G, 'T': T, 'grid': grid, 'a': a, 'b': b, 'ax': ax, 'n': len(G), 'H': operator(G, a, b, ax, len(G))}

# ------------------------------------------------------------------ plaquettes and two-cycles (definitions section 4)
def q8class(W):
    """1, -1, or the axis k of a traceless element (W = +-q_k, q_k = -i sigma_k)"""
    tr = np.real(np.trace(W, axis1=-2, axis2=-1)); out = np.full(len(W), -9)
    out[np.isclose(tr, 2)] = 10; out[np.isclose(tr, -2)] = 11
    trl = np.isclose(tr, 0)
    for k in range(3):
        ck = np.isclose(np.abs(np.einsum('nij,ji->n', W, SIG[k])), 2) & trl; out[ck] = k
    assert (out != -9).all(); return out                                         # 10: +1, 11: -1, 0/1/2: traceless axis
def plaquettes(S):
    """for every lattice edge with its four surrounding cubes owned and >= 2 owners: holonomy class; returns (edge keys, classes)"""
    grid, G = S['grid'], S['G']; N = grid.shape[0]; keys, cls = [], []
    for ax in range(3):
        b_, c_ = [x for x in range(3) if x != ax]
        P = np.stack(np.meshgrid(*[np.arange(N) if k == ax else np.arange(1, N) for k in range(3)], indexing='ij'), -1).reshape(-1, 3)
        def cube(dp):
            q = P.copy(); q[:, b_] -= dp[0]; q[:, c_] -= dp[1]; return q
        cubes = [cube((1, 1)), cube((0, 1)), cube((0, 0)), cube((1, 0))]            # cyclic around the edge
        own = np.stack([grid[q[:, 0], q[:, 1], q[:, 2]] for q in cubes], 1)
        m = (own >= 0).all(1) & (np.array([len(set(r)) for r in own]) >= 2)
        own = own[m]; W = np.tile(np.eye(2, dtype=complex), (len(own), 1, 1))
        steps = [(0, 1, b_), (1, 2, c_), (2, 3, b_), (3, 0, c_)]
        for i, j, axis in steps:
            x, y = own[:, i], own[:, j]; diff = x != y; U = np.tile(np.eye(2, dtype=complex), (len(own), 1, 1))
            if diff.any(): U[diff] = links(G, x[diff], y[diff], axis)
            W = np.einsum('nij,njk->nik', W, U)
        keys.append(np.c_[np.full(m.sum(), ax), P[m]]); cls.append(q8class(W))
    return np.concatenate(keys), np.concatenate(cls)
def trace_of(cls):
    """SU(2)-gauge-invariant part of a class label: 10 (W = 1), 11 (W = -1), 3 (traceless, any axis)"""
    return np.where(cls >= 10, cls, 3)
def class_counts(cls):
    c = collections.Counter(cls.tolist()); return {'+1': c[10], '-1': c[11], 'i': c[0], 'j': c[1], 'k': c[2]}
def two_cycles(S):
    """tile pairs sharing panels with two different normals: holonomy U(a->b via k) U(b->a via l), classes"""
    a, b, ax, G = S['a'], S['b'], S['ax'], S['G']; pair_ax = collections.defaultdict(set)
    for x, y, z in zip(a.tolist(), b.tolist(), ax.tolist()): pair_ax[(min(x, y), max(x, y))].add(z)
    rows = [(x, y, k, l) for (x, y), s in pair_ax.items() for k, l in itertools.combinations(sorted(s), 2)]
    if not rows: return np.zeros((0, 4), int), np.zeros(0, int)
    R = np.array(rows); W = np.einsum('nij,njk->nik', links(G, R[:, 0], R[:, 1], R[:, 2]), links(G, R[:, 1], R[:, 0], R[:, 3]))
    return R, q8class(W)

# ------------------------------------------------------------------ spectra and certificates
def lam_min(H, k=2):
    if H.shape[0] <= 4096: return float(np.linalg.eigvalsh(H.toarray())[0])
    return float(sla.eigsh(H, k=k, which='SA', tol=1e-12, return_eigenvectors=False).min())
U_ROUND = 2.0 ** -53
def cholesky_lower(A, nb=96):
    """phase7_ims.cholesky_lower (same algorithm; Higham 2002 Thm 10.3 applies)"""
    N = A.shape[0]
    for k in range(0, N, nb):
        e = min(k + nb, N)
        for j in range(k, e):
            s = A[j, j] - A[j, k:j] @ A[j, k:j]
            if not s > 0: return False
            A[j, j] = math.sqrt(s)
            if j + 1 < N: A[j + 1:, j] = (A[j + 1:, j] - A[j + 1:, k:j] @ A[j, k:j]) / A[j, j]
        if e < N:
            Pn = A[e:, k:e]; A[e:, e:] -= Pn @ Pn.T
    return True
def certified_lower(H, mu):
    """rigorous: lambda_min(H) >= mu - delta, from a floating Cholesky of the real form of H - mu (H with Gaussian-integer
    entries, mu a dyadic rational with few bits, so H - mu is exact in floating point)"""
    Hd = H.toarray(); assert np.array_equal(Hd.real, np.rint(Hd.real)) and np.array_equal(Hd.imag, np.rint(Hd.imag))
    n = Hd.shape[0]; A = np.zeros((2 * n, 2 * n)); A[:n, :n] = Hd.real; A[n:, n:] = Hd.real; A[:n, n:] = -Hd.imag; A[n:, :n] = Hd.imag
    A[np.arange(2 * n), np.arange(2 * n)] -= float(mu); A = np.tril(A)
    if not cholesky_lower(A): return None
    L = np.tril(A); N = 2 * n; gam = (N + 1) * U_ROUND / (1 - (N + 1) * U_ROUND)
    fro2 = float(np.sum(L * L)) * (1 + 2 * (N * N + 1) * U_ROUND); return float(mu) - gam * fro2 * 1.0001
def rayleigh_upper(H):
    """exact rational Rayleigh quotient of the rounded lowest eigenvector (integer vector) -> rigorous upper bound"""
    w, V = np.linalg.eigh(H.toarray()) if H.shape[0] <= 4096 else sla.eigsh(H, k=2, which='SA', tol=1e-12)
    v = V[:, int(np.argmin(w))]; v = v / np.abs(v).max(); s = 2 ** 20
    xr = np.rint(v.real * s).astype(np.int64); xi = np.rint(v.imag * s).astype(np.int64)
    Re = H.real.tocsr().astype(np.int64); Im = H.imag.tocsr().astype(np.int64)
    yr = Re @ xr - Im @ xi; yi = Re @ xi + Im @ xr
    num = sum(int(p) * int(q) for p, q in zip(xr, yr)) + sum(int(p) * int(q) for p, q in zip(xi, yi))
    den = sum(int(p) * int(p) for p in xr) + sum(int(p) * int(p) for p in xi)
    return Fraction(num, den)

# ------------------------------------------------------------------ S3 action on decorations (rigid axis permutations)
def conj_dec(dec, Q):
    """the decoration of the tiling rotated by the axis permutation Q (frames G -> Q G Q^T, translations T -> Q T)"""
    Qm = pmat(Q)
    def conj_perm(p):
        M = Qm @ pmat(p) @ Qm.T; return tuple(int(np.argmax(M[i])) for i in range(3))
    out = {'0': conj_perm(dec['0'])}
    for v in U3:
        w = tuple(int(x) for x in Qm @ np.array(v)); out[w] = conj_perm(dec[v])
    return out
def index_of(dec):
    d = [EVEN.index(dec['0'])] + [(EVEN if sum(v) % 2 == 0 else ODD).index(dec[v]) for v in U3]
    return sum(x * 3 ** k for k, x in enumerate(d))

# ------------------------------------------------------------------ subcommands
def cmd_pair():
    import phase5b_sweep as sw
    out = {'decorations': {}, 'orbits': {}, 'levels': {}}
    for r in (937, 938):
        assert decoration(r) == sw.decoration(r); out['decorations'][r] = {str(k): v for k, v in decoration(r).items()}
        orb = sorted({index_of(conj_dec(decoration(r), Q)) for Q in PERMS}); out['orbits'][r] = orb
    out['same_orbit'] = 938 in out['orbits'][937]
    out['difference'] = 'centre child only: pi_0 = %s (937) vs %s (938), the two 120-degree rotations about (1,1,1)' % (decoration(937)['0'], decoration(938)['0'])
    log('orbits', out['orbits'], 'same orbit:', out['same_orbit'])
    for L in (3, 4, 5):
        A = build([decoration(937)] * L); B = build([decoration(938)] * L, ref=A['grid']); S = {937: A, 938: B}
        assert np.array_equal(A['grid'] >= 0, B['grid'] >= 0) and all(np.array_equal(A[k], B[k]) for k in ('a', 'b', 'ax'))   # same geometry
        same_tiles = bool(np.array_equal(A['T'], B['T']))
        pk, pa = plaquettes(A); _, pb = plaquettes(B); tk, ta = two_cycles(A); _, tb = two_cycles(B)
        row = {'tiles': A['n'], 'panels': int(len(A['a'])), 'tile_translations_identical': same_tiles,
               'frames_differ_fraction': float((A['G'] != B['G']).any((1, 2)).mean()),
               'plaquettes': int(len(pa)), 'class_counts': {r: class_counts(c) for r, c in ((937, pa), (938, pb))},
               'trace_counts_equal': collections.Counter(trace_of(pa).tolist()) == collections.Counter(trace_of(pb).tolist()),
               'plaquettes_with_different_class': int((pa != pb).sum()), 'plaquettes_with_different_trace': int((trace_of(pa) != trace_of(pb)).sum()),
               'two_cycles': int(len(ta)), 'two_cycle_class_counts': {r: class_counts(c) for r, c in ((937, ta), (938, tb))},
               'two_cycles_with_different_class': int((ta != tb).sum()), 'two_cycles_with_different_trace': int((trace_of(ta) != trace_of(tb)).sum())}
        row['Y'] = {r: lam_min(S[r]['H']) for r in (937, 938)}
        if L == 3:
            for r in (937, 938):
                q = rayleigh_upper(S[r]['H']); mu = Fraction(math.floor((row['Y'][r] - 1e-6) * 2 ** 20), 2 ** 20)
                row.setdefault('certified', {})[r] = {'upper_exact': f'{q.numerator}/{q.denominator}', 'upper': float(q), 'lower': certified_lower(S[r]['H'], mu)}
            row['certified_separation'] = row['certified'][937]['lower'] - row['certified'][938]['upper']
        out['levels'][L] = row; log(f"L{L}:", {k: v for k, v in row.items() if k not in ('class_counts', 'two_cycle_class_counts')})
    save('pair', out)

def int_moments(H, pmax):
    """exact tr(A^p), A = 24 - H (Gaussian integers), p = 1..pmax, plus per-tile local traces; int64 is safe for |A^p| <= 24^p"""
    A = (24 * sps.identity(H.shape[0]) - H).tocsr(); Ar = A.real.astype(np.int64).tocsr(); Ai = A.imag.astype(np.int64).tocsr()
    n2 = H.shape[0]; Xr = np.eye(n2, dtype=np.int64); Xi = np.zeros((n2, n2), dtype=np.int64); tr, loc = [], []
    for p in range(1, pmax + 1):
        assert 24 ** p < 2 ** 62
        Xr, Xi = Ar @ Xr - Ai @ Xi, Ar @ Xi + Ai @ Xr
        d = np.diag(Xr); tr.append(sum(int(x) for x in d)); loc.append(d.reshape(-1, 2).sum(1))   # spinor trace per tile
        assert not np.diag(Xi).any()
    return tr, loc

def cmd_moments(pmax=12, L=3):
    A = build([decoration(937)] * L); S = {937: A, 938: build([decoration(938)] * L, ref=A['grid'])}; out = {'L': L, 'pmax': pmax}
    M = {r: int_moments(S[r]['H'], pmax) for r in (937, 938)}
    out['trace'] = {r: [str(x) for x in M[r][0]] for r in (937, 938)}
    diff = [p for p in range(1, pmax + 1) if M[937][0][p - 1] != M[938][0][p - 1]]; out['first_global_difference'] = diff[0] if diff else None
    # local moments: first order at which the spinor-traced local moment of a tile differs, and where those tiles sit
    G = S[937]['G']; n = S[937]['n']; first = np.full(n, 0)
    for p in range(pmax, 0, -1):
        d = M[937][1][p - 1] != M[938][1][p - 1]; first[d] = p
    # depth of the seam a tile is closest to: the depth at which its subtree differs from its nearest differing neighbour
    a, b = S[937]['a'], S[937]['b']; sd = np.full(n, L + 1)
    for d_ in range(1, L + 1):
        anc = np.arange(n) // 8 ** (L - d_); cross = anc[a] != anc[b]; on = np.zeros(n, bool); on[a[cross]] = True; on[b[cross]] = True
        sd[on & (sd > L)] = d_
    out['local_first_difference_histogram'] = {int(p): int((first == p).sum()) for p in np.unique(first)}
    out['by_seam_depth'] = {int(d_): {int(p): int(((first == p) & (sd == d_)).sum()) for p in np.unique(first)} for d_ in np.unique(sd)}
    if diff:
        p0 = diff[0]; dl = M[937][1][p0 - 1] - M[938][1][p0 - 1]
        out['p0_local_difference'] = {'sum': int(dl.sum()), 'tiles_nonzero': int((dl != 0).sum()), 'values': collections.Counter(dl[dl != 0].tolist())}
    log('moments:', {k: v for k, v in out.items() if k != 'trace'})
    save('moments', out)

def blocks(S):
    """B_ab = sum of the links over the panels a -> b (2x2), as a dict"""
    B = collections.defaultdict(lambda: np.zeros((2, 2), complex)); U = links(S['G'], S['a'], S['b'], S['ax'])
    for x, y, u in zip(S['a'].tolist(), S['b'].tolist(), U): B[(x, y)] += u; B[(y, x)] += u.conj().T
    return B
def walk4(S):
    """tr(A^4) split by the pattern of the closed walk a-b-c-d-a (consecutive tiles differ):
    P1 a=c,b=d (two tiles); P2 a=c,b!=d (two blocks at one tile; the rotated pattern b=d,a!=c gives the same sum); P4 all distinct"""
    B = blocks(S); nb = collections.defaultdict(list)
    for (x, y) in B: nb[x].append(y)
    BB = {k: B[k] @ B[(k[1], k[0])] for k in B}                                  # B_ab B_ba = B_ab B_ab^+, a scalar times I for these links
    P1 = sum(np.trace(BB[k] @ BB[k]).real for k in BB)
    P2 = sum(np.trace(BB[(a, b)] @ BB[(a, d)]).real for a in nb for b in nb[a] for d in nb[a] if b != d)
    P4 = 0.0
    for a in nb:
        for b in nb[a]:
            Bab = B[(a, b)]
            for c in nb[b]:
                if c == a: continue
                Babc = Bab @ B[(b, c)]
                for d in nb[c]:
                    if d == b or d == a or (a, d) not in B: continue
                    P4 += np.trace(Babc @ B[(c, d)] @ B[(d, a)]).real
    scalar = max(float(np.abs(BB[k] - BB[k][0, 0] * np.eye(2)).max()) for k in BB)
    return {'P1': round(P1), 'P2': round(P2), 'P4': round(P4), 'total': round(P1 + 2 * P2 + P4), 'BB_is_scalar_err': scalar}

def cmd_loops(L=3):
    A = build([decoration(937)] * L); S = {937: A, 938: build([decoration(938)] * L, ref=A['grid'])}; out = {'L': L}
    out['walk4'] = {r: walk4(S[r]) for r in (937, 938)}
    # plaquette classes split by the number of distinct owners around the lattice edge
    by = {}
    for r in (937, 938):
        keys, cls = plaquettes(S[r]); grid = S[r]['grid']; nown = []
        for (ax, x, y, z) in keys.tolist():
            b_, c_ = [k for k in range(3) if k != ax]; P = np.array([x, y, z]); cs = []
            for dp in ((1, 1), (0, 1), (0, 0), (1, 0)):
                q = P.copy(); q[b_] -= dp[0]; q[c_] -= dp[1]; cs.append(int(grid[q[0], q[1], q[2]]))
            nown.append(len(set(cs)))
        nown = np.array(nown); by[r] = {int(k): class_counts(cls[nown == k]) for k in (2, 3, 4)}
    out['plaquette_classes_by_owner_count'] = by
    # where the edge difference lives in walk length: l_p = (1/p) log(tr A938^p / tr A937^p) from the full spectra (float)
    ev = {r: 24 - np.linalg.eigvalsh(S[r]['H'].toarray()) for r in (937, 938)}
    def ltr(e, p): m = np.abs(e).max(); return p * np.log(m) + np.log(np.sum((e / m) ** p))
    asym = float(np.log(ev[938].max() / ev[937].max())); lp = {p: float((ltr(ev[938], p) - ltr(ev[937], p)) / p) for p in (4, 6, 8, 12, 16, 24, 32, 48, 64, 96, 128, 192, 256, 384, 512, 1024, 2048)}
    out['moment_log_ratio'] = {'asymptote_log_lmax_ratio': asym, 'l_p': lp, 'fraction_of_asymptote': {p: v / asym for p, v in lp.items()}}
    log('loops:', json.dumps(out, default=float)[:1500]); save('loops', out)

def inflate(G, T, dec):
    o = ops(dec); g = np.stack([x for x, _ in o]); t = np.stack([y for _, y in o])
    return np.einsum('nij,cjk->ncik', G, g).reshape(-1, 3, 3), (2 * T[:, None, :] + np.einsum('nij,cj->nci', G, t)).reshape(-1, 3)
def patch_H(G, T):
    """pinned operator 24 - A on an arbitrary finite set of tiles (compression of the hull operator if the patch is legal)"""
    C = (np.einsum('nij,uj->nui', G, BASE) + 2 * T[:, None, :] - 1) // 2; lo = C.reshape(-1, 3).min(0); C = C - lo
    grid = -np.ones(tuple(C.reshape(-1, 3).max(0) + 1), dtype=np.int64); grid[C[..., 0], C[..., 1], C[..., 2]] = np.arange(len(G))[:, None]
    a, b, ax = panels(grid); return operator(G, a, b, ax, len(G))
OFF1 = np.array([o for o in itertools.product(range(-1, 3), repeat=3) if o != (2, 2, 2)])
def one_star_types(S):
    """complete 1-stars of the supertile S: type key -> representative tile list (definitions section 2)"""
    G, T, grid = S['G'], S['T'], S['grid']; N = grid.shape[0]
    C = (np.einsum('nij,oj->noi', G, 2 * OFF1 + 1) + 2 * T[:, None, :] - 1) // 2      # global cubes of the 63 local offsets
    inside = ((C >= 0) & (C < N)).all(-1).all(-1); types = {}
    for t in np.nonzero(inside)[0]:
        own = grid[C[t, :, 0], C[t, :, 1], C[t, :, 2]]
        if (own < 0).any(): continue
        mem = sorted(set(own.tolist())); Gt = G[t]
        key = tuple(sorted((tuple((Gt.T @ G[b]).ravel().tolist()), tuple((Gt.T @ (T[b] - T[t])).tolist())) for b in mem))
        types.setdefault(key, mem)
    return types

def cmd_ladder01(): cmd_ladder(1, 5, 'ladder_m01')

def lam_min_sparse(H):
    if H.shape[0] <= 512: return float(np.linalg.eigvalsh(H.toarray())[0])
    return float(sla.eigsh(H, k=2, which='SA', tol=1e-10, ncv=40, return_eigenvectors=False).min())

def cmd_ladder(mmax=3, L=5, tag='ladder', topk=20):
    """U_m(r) = min over legal 1-star types tau of rule r of lambda_min(H | sigma^m(tau)): m = 0, 1, 2 over all types found in the
    level-L supertile, m = 3 over the topk types with the lowest U_2 (a minimum over a subset of legal patches is still an
    upper bound on the hull floor, and the two rules are treated alike)"""
    import phase5b_sweep as sw
    rules = {'937': decoration(937), '938': decoration(938), 'FR30': decoration(sw.FR30_INDEX)}; out = {'L_source': L, 'topk_m3': topk, 'rules': {}}
    for name, dec in rules.items():
        S = build([dec] * L); types = list(one_star_types(S).values()); U = np.full((len(types), mmax + 1), np.inf); pat = []
        for i, mem in enumerate(types):
            G, T = S['G'][mem], S['T'][mem]
            for m in range(min(mmax, 2) + 1):
                if m: G, T = inflate(G, T, dec)
                U[i, m] = lam_min_sparse(patch_H(G, T))
            pat.append((G, T))
        if mmax >= 3:
            for i in np.argsort(U[:, 2])[:topk]:
                G, T = inflate(*pat[i], dec); U[i, 3] = lam_min_sparse(patch_H(G, T))
        out['rules'][name] = {'types': len(types), 'U_m': [float(U[:, m].min()) for m in range(mmax + 1)], 'argmin': [int(U[:, m].argmin()) for m in range(mmax + 1)],
                              'lowest_m': {m: np.sort(U[:, m][np.isfinite(U[:, m])])[:6].tolist() for m in range(mmax + 1)}}
        log(f"ladder {name}: {len(types)} types; U_m = {np.round(out['rules'][name]['U_m'], 6).tolist()}")
    d = {m: out['rules']['938']['U_m'][m] - out['rules']['937']['U_m'][m] for m in range(mmax + 1)}; out['diff_938_minus_937'] = d
    log('ladder: 938 - 937 by m:', {m: round(v, 5) for m, v in d.items()}); save(tag, out)

def cmd_steps():
    """centre choice per substitution step: s_j = 1 (937, pi_0 = (1,2,0)) or 2 (938, pi_0 = (2,0,1)); octants fixed (identical in both)"""
    base = decoration(937); out = {'levels': {}}
    def dec_c(c):
        d = dict(base); d['0'] = EVEN[c]; return d
    for L in (3, 4, 5):
        rows = []; ref = build([dec_c(1)] * L)['grid']
        for s in itertools.product((1, 2), repeat=L):
            S = build([dec_c(c) for c in s], ref=ref); _, cls = plaquettes(S) if L <= 4 else (None, None)
            rows.append({'s': ''.join(map(str, s)), 'Y': lam_min(S['H']), 'class_counts': class_counts(cls) if cls is not None else None})
            log(f"steps L{L} s={rows[-1]['s']}: Y {rows[-1]['Y']:.6f}")
        Y = {r['s']: r['Y'] for r in rows}
        main = {j + 1: float(np.mean([Y[k] for k in Y if k[j] == '2']) - np.mean([Y[k] for k in Y if k[j] == '1'])) for j in range(L)}
        single = {j + 1: Y['1' * j + '2' + '1' * (L - j - 1)] - Y['1' * L] for j in range(L)}
        cc = [json.dumps(r['class_counts'], sort_keys=True) for r in rows if r['class_counts']]
        out['levels'][L] = {'rows': rows, 'main_effect_of_step': main, 'single_flip_from_937': single, 'Y937': Y['1' * L], 'Y938': Y['2' * L],
                            'distinct_class_count_vectors': len(set(cc)) if cc else None}
        log(f"steps L{L}: main effects {main}; single flips {single}")
    save('steps', out)

if __name__ == '__main__':
    for c in sys.argv[1:]: globals()[f'cmd_{c}']()
