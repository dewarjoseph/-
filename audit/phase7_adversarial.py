#!/usr/bin/env python3
"""Phase VII (II): adversarial re-certification of the Phase VI level-1 claims, written from scratch (no phase6_* imports).

Representation.  Q8 = {+-1, +-q1, +-q2, +-q3} as an 8-element table group (index = 2*u + s, u in {0: 1, 1: q1, 2: q2, 3: q3},
s = sign bit), with the Hamilton product q1 q2 = q3, q2 q3 = q1, q3 q1 = q2, qi^2 = -1, realised as SU(2) matrices
q_k = -i sigma_k (checked).  For signed coordinate axes u = s_u e_i, v = s_v e_j the Pauli identity gives
   (sigma.u)(sigma.v) = s_u s_v I                     (i = j)
                      = s_u s_v eps_ijk i sigma_k = -s_u s_v eps_ijk q_k     (i != j),
so every link C_ab = (sigma.M_a^T e_k)(sigma.M_b^T e_k) is computed as a table element without matrices.
Geometry.  The level-1 supertile is rebuilt from its geometric description: the side-4 chair [0,4)^3 minus [2,4)^3 split into the
centre chair (2x2x2 block at (1,1,1), missing corner (+,+,+)) and seven octant chairs (2x2x2 block at 2v, missing corner in
direction s(v) = 1 - 2v); cross-checked against the substitution formula.  A frame M is compatible with a chair whose missing
corner points in direction sigma iff M = D_sigma P_pi (any of the 6 permutations pi); proper iff det M = 1.
Checks (results -> audit/results/phase7_adversarial.json):
  1  all 6^8 = 1 679 616 compatible frame choices: links, every fundamental-cycle holonomy (BFS tree, explicit table products),
     pure gauge or not, the 21 two-cycle configurations and how many are non-trivial; the proper subset (3^8 = 6561) separately;
  2  lambda_min of the free connection Laplacian for every choice (batched eigvalsh), gauge-class reduction by the tree-gauge key,
     exact Bareiss/Sylvester certification of lambda_min >= c for every class (proper) and of the improper minimum;
  3  zero-mode lemma: free vs pinned operators, kernel dimensions, connectedness.
"""
import os, sys, json, time, itertools, collections
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); RES = os.path.join(HERE, 'results')
import numpy as np
from fractions import Fraction
T0 = time.time()
def log(*a): print(f"[{time.time()-T0:6.0f}s]", *a, flush=True)

# ------------------------------------------------------------------ Q8 as a table group
SIG = [np.array([[0, 1], [1, 0]], complex), np.array([[0, -1j], [1j, 0]], complex), np.array([[1, 0], [0, -1]], complex)]
UNITS = [np.eye(2, dtype=complex)] + [-1j * S for S in SIG]                 # 1, q1, q2, q3
def elem(u, s): return 2 * u + s                                          # s = 0: +, 1: -
MAT = [((-1) ** (e % 2)) * UNITS[e // 2] for e in range(8)]
def idx_of(M):
    for e in range(8):
        if np.abs(MAT[e] - M).max() < 1e-12: return e
    raise ValueError
MUL = np.array([[idx_of(MAT[a] @ MAT[b]) for b in range(8)] for a in range(8)], np.int8)
INVQ = np.array([idx_of(np.linalg.inv(MAT[a])) for a in range(8)], np.int8)
assert idx_of(MAT[2] @ MAT[4]) == 6 and idx_of(MAT[2] @ MAT[2]) == 1            # q1 q2 = q3, q1^2 = -1 (Hamilton)
EPS = np.zeros((3, 3, 3), int)
for (i, j, k), s in {(0, 1, 2): 1, (1, 2, 0): 1, (2, 0, 1): 1, (0, 2, 1): -1, (2, 1, 0): -1, (1, 0, 2): -1}.items(): EPS[i, j, k] = s
def link_q(Ma, Mb, k):
    """(sigma.M_a^T e_k)(sigma.M_b^T e_k) as a Q8 table index, via the Pauli identity (no matrices)."""
    ua, ub = Ma[k], Mb[k]                                                  # rows: M^T e_k = row k of M
    i = int(np.nonzero(ua)[0][0]); j = int(np.nonzero(ub)[0][0]); s = int(ua[i] * ub[j])
    if i == j: return elem(0, 0 if s == 1 else 1)
    kk = 3 - i - j; sign = -s * EPS[i, j, kk]                               # -s_u s_v eps_ijk q_k
    return elem(kk + 1, 0 if sign == 1 else 1)
for _ in range(200):                                                       # check against matrices
    rng = np.random.default_rng(_); P1 = np.eye(3, dtype=int)[rng.permutation(3)] * rng.choice([-1, 1], (3, 1)); P2 = np.eye(3, dtype=int)[rng.permutation(3)] * rng.choice([-1, 1], (3, 1))
    k = int(rng.integers(3)); M = sum(P1[k][t] * SIG[t] for t in range(3)) @ sum(P2[k][t] * SIG[t] for t in range(3))
    assert idx_of(M) == link_q(P1, P2, k)

# ------------------------------------------------------------------ level-1 geometry from its geometric description
U3 = [v for v in itertools.product((0, 1), repeat=3) if v != (1, 1, 1)]
def chair_cubes(origin, sigma):
    """2x2x2 block at origin minus the corner cube in direction sigma (sigma_i = +1: high side)."""
    miss = tuple(origin[i] + (1 if sigma[i] == 1 else 0) for i in range(3))
    return frozenset(tuple(origin[i] + d[i] for i in range(3)) for d in itertools.product((0, 1), repeat=3)) - {miss}
CHILDREN = [((1, 1, 1), (1, 1, 1))] + [(tuple(2 * x for x in v), tuple(1 - 2 * x for x in v)) for v in U3]   # (origin, missing-corner direction)
TILES = [chair_cubes(o, s) for o, s in CHILDREN]
SIGMAS = [s for _, s in CHILDREN]
allc = [c for t in TILES for c in t]; assert len(allc) == len(set(allc)) == 56
assert set(allc) == {c for c in itertools.product(range(4), repeat=3) if not all(x >= 2 for x in c)}
def cross_check_with_substitution():
    from independent_clifford_q8_audit import FR30, tiles_at_level          # V-A independent audit module (not Phase VI code)
    tl = tiles_at_level(FR30, 1); return sorted(sorted(t[2]) for t in tl) == sorted(sorted(t) for t in TILES)
OWN = {c: a for a, t in enumerate(TILES) for c in t}
PANELS = []                                                                # (a, b, axis) per shared unit face, a = lower cube owner
for c, a in OWN.items():
    for k in range(3):
        c2 = list(c); c2[k] += 1; b = OWN.get(tuple(c2))
        if b is not None and b != a: PANELS.append((a, b, k))
PERMS = list(itertools.permutations(range(3)))
def frame(t, pi):
    D = np.diag(SIGMAS[t]); P = np.zeros((3, 3), int)
    for i in range(3): P[i, PERMS[pi][i]] = 1
    return D @ P
FR = [[frame(t, p) for p in range(6)] for t in range(8)]
DET = np.array([[round(np.linalg.det(FR[t][p])) for p in range(6)] for t in range(8)])
for t in range(8):                                                        # compatibility: M maps the base chair onto the tile (up to translation)
    base = chair_cubes((0, 0, 0), (1, 1, 1))
    for p in range(6):
        img = {tuple(int(x) for x in (FR[t][p] @ (2 * np.array(c) - 1))) for c in base}        # doubled centred coordinates
        tgt = {tuple(2 * (c[i] - CHILDREN[t][0][i]) - 1 for i in range(3)) for c in TILES[t]}
        assert img == tgt, 'frame not geometry-compatible'
LQ = np.zeros((len(PANELS), 6, 6), np.int8)
for f, (a, b, k) in enumerate(PANELS):
    for pa in range(6):
        for pb in range(6): LQ[f, pa, pb] = link_q(FR[a][pa], FR[b][pb], k)

# two-cycle configurations from the incidence structure
# unordered tile pairs; a panel stored as (b, a, k) is used with the inverse link when the pair is read as (a, b), a < b
PAIRAX = collections.defaultdict(set); PANEL_OF = {}
for f, (a, b, k) in enumerate(PANELS):
    lo, hi = min(a, b), max(a, b); PAIRAX[(lo, hi)].add(k); PANEL_OF.setdefault((lo, hi, k), (f, +1 if a == lo else -1))
TWO = [((a, b), k, l) for (a, b), ks in PAIRAX.items() for k in ks for l in ks if k < l]
FORCED = [i for i, ((a, b), k, l) in enumerate(TWO) if SIGMAS[a][3 - k - l] != SIGMAS[b][3 - k - l]]

# BFS spanning tree for fundamental cycles
ADJ = collections.defaultdict(list)
for f, (a, b, k) in enumerate(PANELS): ADJ[a].append((b, f, +1)); ADJ[b].append((a, f, -1))
PARENT = {0: None}; ORDER = [0]; TREE = set(); qd = collections.deque([0])
while qd:
    u = qd.popleft()
    for v, f, o in ADJ[u]:
        if v not in PARENT: PARENT[v] = (u, f, o); TREE.add(f); ORDER.append(v); qd.append(v)
NONTREE = [f for f in range(len(PANELS)) if f not in TREE]

def analyse(P):
    """P: (N, 8) permutation indices.  Returns per-config: number of non-trivial fundamental cycles, number of non-trivial
    two-cycle configurations, whether all FORCED ones are non-trivial, tree-gauge key (Q8 indices of the non-tree links)."""
    N = len(P); L = np.stack([LQ[f][P[:, a], P[:, b]] for f, (a, b, k) in enumerate(PANELS)], 1)        # (N, F) link indices
    Pth = np.zeros((N, 8), np.int8)                                         # path product root -> x (Q8 index), root = 0 -> identity
    for v in ORDER[1:]:
        u, f, o = PARENT[v]; C = L[:, f] if o == 1 else INVQ[L[:, f]]
        Pth[:, v] = MUL[Pth[:, u], C]
    keys = []
    for f in NONTREE:
        a, b, k = PANELS[f]; W = MUL[MUL[Pth[:, a], L[:, f]], INVQ[Pth[:, b]]]; keys.append(W)
    keys = np.stack(keys, 1)                                                # fundamental-cycle holonomies (= tree-gauge non-tree links)
    nontriv = (keys != 0).sum(1)
    def oriented(a, b, k):
        f, o = PANEL_OF[(a, b, k)]; return L[:, f] if o == 1 else INVQ[L[:, f]]
    tw = np.stack([MUL[oriented(a, b, k), INVQ[oriented(a, b, l)]] for (a, b), k, l in TWO], 1)   # a ->(k) b ->(l) a
    return L, keys, nontriv, (tw != 0).sum(1), (tw[:, FORCED] != 0).all(1), tw

def free_laplacian_batch(L):
    N = len(L); H = np.zeros((N, 16, 16), complex); M8 = np.array(MAT)
    for f, (a, b, k) in enumerate(PANELS):
        C = M8[L[:, f]]
        for i in range(2):
            H[:, 2*a+i, 2*a+i] += 1; H[:, 2*b+i, 2*b+i] += 1
        H[:, 2*a:2*a+2, 2*b:2*b+2] -= C; H[:, 2*b:2*b+2, 2*a:2*a+2] -= np.conj(np.transpose(C, (0, 2, 1)))
    return H

def bareiss_posdef(Re, Im, p, q):
    n = Re.shape[0]; A = [[(q * int(Re[i, j]) - (p if i == j else 0), q * int(Im[i, j])) for j in range(n)] for i in range(n)]; prev = 1
    for k in range(n):
        pr, pim = A[k][k]; assert pim == 0
        if pr <= 0: return False
        for i in range(k + 1, n):
            air, aii = A[i][k]
            for j in range(k + 1, n):
                xr, xi = A[i][j]; bkr, bki = A[k][j]
                nr = pr * xr - (air * bkr - aii * bki); ni = pr * xi - (air * bki + aii * bkr)
                qr, rr = divmod(nr, prev); qi, ri = divmod(ni, prev); assert rr == 0 and ri == 0; A[i][j] = (qr, qi)
        prev = pr
    return True

def main():
    out = {'geometry_matches_substitution': cross_check_with_substitution(), 'tiles': 8, 'panels': len(PANELS), 'fundamental_cycles': len(NONTREE),
           'two_cycle_configurations': len(TWO), 'forced_configurations_by_geometry': len(FORCED),
           'forced_list': [[[int(TWO[i][0][0]), int(TWO[i][0][1])], int(TWO[i][1]), int(TWO[i][2])] for i in FORCED]}
    log(f"geometry = substitution: {out['geometry_matches_substitution']}; panels {len(PANELS)}, fundamental cycles {len(NONTREE)}, "
        f"two-cycle configurations {len(TWO)}, forced by geometry {len(FORCED)}")
    ALL = np.array(list(itertools.product(range(6), repeat=8)), np.int8)
    proper = np.all(DET[np.arange(8)[None, :], ALL] == 1, axis=1)
    log(f"configurations: {len(ALL)}, proper {int(proper.sum())}")
    res = {'nontriv_cycles': [], 'nontriv_two': [], 'forced_ok': [], 'lam': [], 'keys': []}
    for s in range(0, len(ALL), 100000):
        P = ALL[s:s + 100000]; L, keys, nt, ntw, fok, tw = analyse(P)
        lam = np.linalg.eigvalsh(free_laplacian_batch(L))[:, 0]
        res['nontriv_cycles'].append(nt); res['nontriv_two'].append(ntw); res['forced_ok'].append(fok); res['lam'].append(lam); res['keys'].append(keys)
        log(f"  {s + len(P)}/{len(ALL)} done")
    for k in res: res[k] = np.concatenate(res[k])
    nt, ntw, fok, lam, keys = res['nontriv_cycles'], res['nontriv_two'], res['forced_ok'], res['lam'], res['keys']
    for tag, m in (('proper', proper), ('improper', ~proper), ('all', np.ones(len(ALL), bool))):
        sub = {'count': int(m.sum()), 'pure_gauge': int((nt[m] == 0).sum()), 'min_nontrivial_fundamental_cycles': int(nt[m].min()),
               'min_nontrivial_two_cycle_configs': int(ntw[m].min()), 'all_forced_nontrivial': bool(fok[m].all()), 'forced_failures': int((~fok[m]).sum()),
               'lambda_min': {'min': float(lam[m].min()), 'argmin': ALL[m][int(np.argmin(lam[m]))].tolist(), 'median': float(np.median(lam[m])), 'max': float(lam[m].max())}}
        out[tag] = sub; log(f"{tag}: {sub}")
    # smallest counterexamples (improper): pure gauge, or forced two-cycle trivial
    imp = np.nonzero(~proper)[0]
    pg = imp[nt[imp] == 0]; out['improper_pure_gauge_examples'] = ALL[pg[:5]].tolist()
    ff = imp[~fok[imp]]
    if len(ff):
        i0 = ff[np.argmin(ntw[ff])]; out['improper_forced_failure_example'] = {'perms': ALL[i0].tolist(), 'det': DET[np.arange(8), ALL[i0]].tolist(),
                                                                                'nontrivial_two_cycle_configs': int(ntw[i0]), 'nontrivial_fundamental_cycles': int(nt[i0])}
    # gauge classes (tree-gauge keys); exact certification per class
    for tag, m, c in (('proper', proper, Fraction(167, 100)), ('proper_sharper', proper, None), ('improper', ~proper, None)):
        ks = keys[m]; uniq, first = np.unique(ks, axis=0, return_index=True); idxs = np.nonzero(m)[0][first]
        lam_cls = lam[idxs]
        cc = c if c is not None else Fraction(int(np.floor(float(lam_cls.min()) * 10 ** 5)) - 1, 10 ** 5)
        t0 = time.time(); fails = []
        Lsel = analyse(ALL[idxs])[0]; Hs = free_laplacian_batch(Lsel)
        for j in range(len(idxs)):
            H = Hs[j]; Re = np.rint(H.real).astype(np.int64); Im = np.rint(H.imag).astype(np.int64)
            if not bareiss_posdef(Re, Im, cc.numerator, cc.denominator): fails.append(int(idxs[j]))
        jmin = int(np.argmin(lam_cls)); H = Hs[jmin]; above = Fraction(int(np.floor(float(lam_cls[jmin]) * 10 ** 5)) + 1, 10 ** 5)
        rejects = not bareiss_posdef(np.rint(H.real).astype(np.int64), np.rint(H.imag).astype(np.int64), above.numerator, above.denominator)
        out[f'certificate_{tag}'] = {'gauge_classes': int(len(idxs)), 'c': f'{cc.numerator}/{cc.denominator}', 'value': float(cc), 'failures': len(fails),
                                     'min_lambda': float(lam_cls.min()), 'rejects_min_plus_1e-5': bool(rejects), 'seconds': time.time() - t0}
        log(f"certificate {tag}: {out[f'certificate_{tag}']}")
    # zero-mode lemma checks on the level-1 supertile
    triv = np.zeros((1, len(PANELS)), np.int8); Hfree = free_laplacian_batch(triv)[0]
    deg = np.real(np.diag(Hfree))[0::2]; Hpin = Hfree + np.diag(np.repeat(24 - deg, 2))
    out['zero_mode'] = {'free_trivial_kernel_dim': int((np.linalg.eigvalsh(Hfree) < 1e-10).sum()), 'pinned_trivial_lambda_min': float(np.linalg.eigvalsh(Hpin)[0]),
                        'note': 'pinned operator has trivial kernel for every connection (boundary term > 0 on a connected graph)'}
    log(f"zero modes: {out['zero_mode']}")
    json.dump(out, open(os.path.join(RES, 'phase7_adversarial.json'), 'w'), indent=1)

if __name__ == '__main__': main()
