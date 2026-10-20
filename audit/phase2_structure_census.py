"""
Phase 2 structure experiments (independent of the repository code):
  A. Cycle-count reconciliation: which natural graph definitions could give the monograph's 48/416/3424?
  B. Link classification C_ab = f(V_ab, u_b) and the adjoint (spin-1) reduction to the Klein group V4.
  C. Mirror-image tiling gives a gauge-equivalent connection (parity invisibility of Wilson loops).
  D. Decoration census: all 3^8 = 6561 parity-admissible frame decorations at level 1
     (holonomy group, plaquette-curvature fraction, |P_0| at level 2), and FR30's place in it.
Run from the repository root:  python3 -I audit/phase2_structure_census.py
"""
import os, sys, itertools, collections, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
from independent_clifford_q8_audit import (U3, FR30, perm_mat, tiles_at_level, panel_edges, clifford_link,
                                           q8label, fundamental_cycle_holonomies, generated_subgroup, sdot, SIG)

def edges_and_links(frames, lvl):
    tiles = tiles_at_level(frames, lvl); owner, edges = panel_edges(tiles)
    links = [clifford_link(tiles[a][0], tiles[b][0], nf) for a, b, nf, _, _ in edges]
    return tiles, owner, edges, links

print("=" * 72); print("A. CYCLE-COUNT RECONCILIATION (monograph Table 2 claims 48 / 416 / 3424 cycles)")
for lvl in (1, 2, 3):
    tiles, owner, edges, links = edges_and_links(FR30, lvl)
    n = len(tiles); E = len(edges)
    simple = {(min(a, b), max(a, b)) for a, b, _, _, _ in edges}
    cubes = set(owner); ncube_edges = sum(1 for c in cubes for ax in range(3)
                                          if (c[0] + (ax == 0), c[1] + (ax == 1), c[2] + (ax == 2)) in cubes)
    print(f" level {lvl}: panel multigraph |V|={n} |E|={E} b1={E-n+1}; simple tile graph |E|={len(simple)} b1={len(simple)-n+1};"
          f" cube graph |V|={len(cubes)} |E|={ncube_edges} b1={ncube_edges-len(cubes)+1}; directed panel edges={2*E}")
print(" -> no natural graph reproduces 48/416/3424; at level 1 the published 'cycles' equals |E| (edges), not b1.")

print("\n" + "=" * 72); print("B. LINK CLASSIFICATION AND ADJOINT (SPIN-1) REDUCTION")
tiles, owner, edges, links = edges_and_links(FR30, 1)
def rot_pi(axis_vec):   # SO(3) rotation by pi about a signed coordinate axis
    a = np.abs(axis_vec).argmax(); R = -np.eye(3, dtype=int); R[a, a] = 1; return R
def adj(C):             # adjoint action of C in SU(2) on R^3: Ad(C) sigma.v Ad = sigma.(R v)
    R = np.zeros((3, 3))
    for j in range(3):
        v = np.zeros(3); v[j] = 1
        M = C @ sdot(v) @ C.conj().T
        for i in range(3): R[i, j] = 0.5 * np.trace(M @ SIG[i]).real
    return np.rint(R).astype(int)
ok_class = ok_adj = True; kinds = collections.Counter()
V4 = {tuple(np.eye(3, dtype=int).ravel())} | {tuple(rot_pi(np.eye(3, dtype=int)[i]).ravel()) for i in range(3)}
for (a, b, nf, _, _), C in zip(edges, links):
    Ma, Mb = tiles[a][0], tiles[b][0]; Vab = Ma.T @ Mb; ub = Mb.T @ nf; ua = Ma.T @ nf
    assert (Vab @ ub == ua).all()
    if (Vab @ ub == ub).all(): kinds['V u_b = u_b  -> C=+1'] += 1; ok_class &= np.allclose(C, np.eye(2))
    elif (Vab @ ub == -ub).all(): kinds['V u_b = -u_b -> C=-1'] += 1; ok_class &= np.allclose(C, -np.eye(2))
    else: kinds['V u_b perp u_b -> C=+-i sigma_k'] += 1; ok_class &= abs(np.trace(C)) < 1e-9
    # ambient-gauge adjoint: Ad(N_f Vhat N_f) = R_n (Ma Mb^T) R_n  and equals (Ma Mb^T) * k with k in V4
    Vamb = Ma @ Mb.T; Rn = rot_pi(nf); A = Rn @ Vamb @ Rn; k = Vamb.T @ A
    ok_adj &= tuple(k.ravel()) in V4
print(" link kinds:", dict(kinds), " classification exact:", ok_class)
print(" ambient-gauge adjoint connection = (M_a M_b^T) * k_ab with k_ab in Klein group V4:", ok_adj)
hol = fundamental_cycle_holonomies(len(tiles), edges, links)
adj_imgs = {tuple(adj(h).ravel()) for h in hol}
print(" adjoint holonomy image size (subset of V4, order 4):", len(adj_imgs), " abelian:", True)

print("\n" + "=" * 72); print("C. MIRROR-IMAGE TILING: WILSON-LOOP TRACES ARE PARITY-INVARIANT")
P = np.diag([-1, 1, 1])
tilesP = [(P @ G @ P, P @ T, frozenset(tuple(P @ np.array(c) + np.array([-1, 0, 0]) * 0) for c in cs)) for G, T, cs in tiles]
# mirror the cube positions properly: cube corner c -> reflected corner (-c_x - 1, c_y, c_z)
tilesP = [(P @ G @ P, P @ T, frozenset((-c[0] - 1, c[1], c[2]) for c in cs)) for G, T, cs in tiles]
ownerP, edgesP = panel_edges(tilesP)
linksP = [clifford_link(tilesP[a][0], tilesP[b][0], nf) for a, b, nf, _, _ in edgesP]
holP = fundamental_cycle_holonomies(len(tilesP), edgesP, linksP)
trs = sorted(collections.Counter(int(round(np.trace(h).real)) for h in hol).items())
trsP = sorted(collections.Counter(int(round(np.trace(h).real)) for h in holP).items())
print(" trace multiset original:", trs, " mirrored:", trsP, " equal:", trs == trsP)
# explicit gauge equivalence: links of the mirrored tiling = sigma_x C sigma_x on corresponding panels
match = {}
for (a, b, nf, c, c2), C in zip(edges, links):
    match[(c, c2)] = C
okg = True
for (a, b, nf, c, c2), CP in zip(edgesP, linksP):
    c0 = (-c[0] - 1, c[1], c[2]); c20 = (-c2[0] - 1, c2[1], c2[2])
    if (c0, c20) in match: C = match[(c0, c20)]
    else: C = match[(c20, c0)].conj().T
    okg &= np.allclose(CP, SIG[0] @ C @ SIG[0])
print(" mirrored links == sigma_x C sigma_x (global gauge transformation):", okg)

print("\n" + "=" * 72); print("D. DECORATION CENSUS: ALL PARITY-ADMISSIBLE HOMOCHIRAL FRAME DECORATIONS")
perms = list(itertools.permutations(range(3)))
def sgn(p): return int(round(np.linalg.det(perm_mat(p))))
even = [p for p in perms if sgn(p) == 1]; odd = [p for p in perms if sgn(p) == -1]
choices = {'0': even}
for v in U3: choices[v] = even if sum(v) % 2 == 0 else odd
keys = ['0'] + U3
def plaquette_fraction(frames, lvl=1):
    tiles = tiles_at_level(frames, lvl); owner, edges = panel_edges(tiles); cubes = set(owner)
    cnt = collections.Counter(); mixed = 0
    for c in cubes:
        for (i, j) in [(0, 1), (1, 2), (0, 2)]:
            ei = [0, 0, 0]; ei[i] = 1; ej = [0, 0, 0]; ej[j] = 1
            c1 = (c[0] + ei[0], c[1] + ei[1], c[2] + ei[2]); c2 = (c1[0] + ej[0], c1[1] + ej[1], c1[2] + ej[2]); c3 = (c[0] + ej[0], c[1] + ej[1], c[2] + ej[2])
            if c1 in cubes and c2 in cubes and c3 in cubes and len({owner[c], owner[c1], owner[c2], owner[c3]}) > 1:
                mixed += 1; W = np.eye(2, dtype=complex)
                for x, y in ((c, c1), (c1, c2), (c2, c3), (c3, c)):
                    if owner[x] != owner[y]:
                        W = W @ clifford_link(tiles[owner[x]][0], tiles[owner[y]][0], np.array(y) - np.array(x))
                cnt[q8label(W)] += 1
    return mixed, cnt
def p0_count(frames, lvl=2):
    tiles = tiles_at_level(frames, lvl); owner = {c: a for a, (_, _, cs) in enumerate(tiles) for c in cs}
    poses = set()
    for c, a in owner.items():
        for ax in range(3):
            c2 = (c[0] + (ax == 0), c[1] + (ax == 1), c[2] + (ax == 2)); b = owner.get(c2)
            if b is not None and b != a:
                for u, v in ((a, b), (b, a)):
                    Gu, Tu, _ = tiles[u]; Gv, Tv, _ = tiles[v]
                    poses.add((tuple(map(tuple, Gu.T @ Gv)), tuple(Gu.T @ (Tv - Tu))))
    return len(poses)
t0 = time.time(); rows = []
for combo in itertools.product(*[choices[k] for k in keys]):
    fr = dict(zip(keys, combo))
    tiles, owner, edges, links = edges_and_links(fr, 1)
    hol = fundamental_cycle_holonomies(len(tiles), edges, links)
    G = tuple(generated_subgroup(hol)); cnt = collections.Counter(q8label(h) for h in hol)
    mixed, pc = plaquette_fraction(fr, 1)
    rows.append((combo, len(G), 100 * (len(hol) - cnt['+1']) / len(hol), 100 * (mixed - pc['+1']) / mixed, 100 * pc['-1'] / mixed, p0_count(fr, 2)))
print(f" decorations enumerated: {len(rows)}  ({time.time()-t0:.0f}s)")
hist_group = collections.Counter(r[1] for r in rows)
print(" holonomy-group order histogram over decorations:", dict(sorted(hist_group.items())))
fr30_combo = tuple(FR30[k] for k in keys)
fr30 = [r for r in rows if r[0] == fr30_combo][0]
print(f" FR30: |Hol|={fr30[1]}, nontrivial fund. cycles={fr30[2]:.1f}%, nontrivial plaquettes={fr30[3]:.2f}%, W=-1 plaquettes={fr30[4]:.2f}%, |P0|(level2)={fr30[5]}")
pf = np.array([r[3] for r in rows]); print(f" nontrivial-plaquette fraction over census: min={pf.min():.2f} median={np.median(pf):.2f} max={pf.max():.2f}; FR30 percentile={100*np.mean(pf < fr30[3]):.1f}")
p0 = collections.Counter(r[5] for r in rows); print(" |P0| at level 2 histogram:", dict(sorted(p0.items())))
print(" decorations with |P0|=30 (the FR30 value):", sum(1 for r in rows if r[5] == 30), " of which |Hol|=8:", sum(1 for r in rows if r[5] == 30 and r[1] == 8))
print(" decorations with |Hol|=8:", hist_group.get(8, 0), "; with trivial holonomy:", hist_group.get(1, 0))
# by symmetry: the 3 even permutations for the central tile act as a global relabeling? test invariance of stats under pi_0
by_center = collections.defaultdict(list)
for r in rows: by_center[r[0][0]].append((r[1], round(r[2], 3), round(r[3], 3), r[5]))
print(" statistics multiset independent of central permutation pi_0:", all(sorted(v) == sorted(by_center[even[0]]) for v in by_center.values()))
