"""
Phase 5a / Task B3: structural facts about the FR30 chair substitution needed for the infinite-volume framework.

  1. Frame-type substitution: which frames G in SO(3,Z) occur, the induced matrix F[G',G] = #{c : G g_c = G'},
     its column/row sums, Perron-Frobenius data and primitivity exponent.
  2. Nesting: the (0,0,0)-octant child of T_{m+1} is T_m with identical poses (hence identical frames, cubes,
     panels and links); the panels among T_m's tiles inside T_{m+1} are exactly the panels of T_m.
  3. Rotation covariance of the link rule: the links of sigma^m(t) for a tile t with frame G equal the links of T_m.
  4. Every chair has exactly 24 external unit faces; in T_m the tiles with degree < 24 (boundary tiles) all touch
     the surface of the supertile; counts b_m and the bound b_m <= 24 * 4^m.
  5. Recognizability ("notch rule"): a chair is the central chair of its level-1 supertile iff at least 2 (in fact
     all 7) of its cubes are notch cubes of other chairs; outer chairs have at most one such cube.  Also the parity
     statement: bounding-box corners are = 0 or (1,1,1) mod 2, the latter exactly for central chairs.
  6. Fixed-point seed: the pose (I, -(1,1,1)) (doubled coordinates) is its own central child; the (0,0,0)-child
     fixed point is the root (I,0), whose nested supertiles exhaust only the octant [0,oo)^3.

Run from the repository root:  python3 -u -I audit/phase5a_frame_substitution.py
"""
import os, sys, itertools, collections, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
from independent_clifford_q8_audit import FR30, U3, perm_mat, tiles_at_level, panel_edges, clifford_link, q8label

OUT = []
def say(*a):
    s = " ".join(str(x) for x in a); print(s, flush=True); OUT.append(s)

def child_ops(frames=FR30):
    ops = [(perm_mat(frames['0']), np.array([1, 1, 1]))]
    for v in U3:
        Ds = np.diag([1 - 2 * v[0], 1 - 2 * v[1], 1 - 2 * v[2]])
        ops.append((Ds @ perm_mat(frames[v]), 4 * np.array(v)))
    return ops

def key(G): return tuple(int(x) for x in np.asarray(G).ravel())

# ---------------------------------------------------------------- 1. frame substitution
say("=" * 78); say("1. FRAME-TYPE SUBSTITUTION")
ops = child_ops()
gens = [g for g, _ in ops]
for (g, t), lab in zip(ops, ['center'] + [str(v) for v in U3]):
    assert round(float(np.linalg.det(g))) == 1 and (g.T @ g == np.eye(3, dtype=int)).all()
say(" child rotational parts g_c (row-major), det=+1 checked:")
for (g, t), lab in zip(ops, ['center'] + [str(v) for v in U3]):
    say(f"   {lab:9s} t={tuple(int(x) for x in t)}  g={key(g)}")
# all signed permutation matrices with det +1 = SO(3,Z), order 24
SO3Z = []
for p in itertools.permutations(range(3)):
    for s in itertools.product((1, -1), repeat=3):
        M = np.diag(s) @ perm_mat(p)
        if round(float(np.linalg.det(M))) == 1: SO3Z.append(M)
assert len(SO3Z) == 24
# frames reachable from the identity by words in the g_c (right multiplication): level-m frames = {g_{c1} ... g_{cm}}
level_frames = [{key(np.eye(3, dtype=int))}]
for m in range(1, 12):
    nxt = set()
    for Gk in level_frames[-1]:
        G = np.array(Gk).reshape(3, 3)
        for g in gens: nxt.add(key(G @ g))
    level_frames.append(nxt)
    say(f" frames occurring at level {m}: {len(nxt)}")
    if len(nxt) == 24: break
Hset = sorted(level_frames[-1])
say(f" set H of occurring frames: |H| = {len(Hset)}  (|SO(3,Z)| = 24)  H = SO(3,Z): {len(Hset) == 24}")
idx = {k: i for i, k in enumerate(Hset)}
F = np.zeros((len(Hset), len(Hset)), dtype=int)
for Gk in Hset:
    G = np.array(Gk).reshape(3, 3)
    for g in gens: F[idx[key(G @ g)], idx[Gk]] += 1
say(" frame substitution matrix F[G',G] = #{children of a G-tile with frame G'}:")
say(" column sums:", sorted(set(F.sum(axis=0).tolist())), " row sums:", sorted(set(F.sum(axis=1).tolist())))
say(" F is a sum of 8 permutation matrices (right multiplications by g_c): doubly stochastic after /8")
ev = np.linalg.eigvals(F.astype(float)); ev = ev[np.argsort(-abs(ev))]
say(" spectrum of F (moduli, sorted):", np.round(np.abs(ev), 6).tolist())
say(" Perron-Frobenius eigenvalue 8 simple:", int(np.sum(np.abs(ev - 8) < 1e-9)) == 1, "; second largest modulus:", round(float(abs(ev[1])), 6))
P = (F > 0).astype(int); Pk = np.eye(len(Hset), dtype=int); prim = None
for k in range(1, 40):
    Pk = ((Pk @ P) > 0).astype(int)
    if Pk.min() > 0: prim = k; break
say(f" primitivity exponent (smallest k with F^k > 0 entrywise): {prim}")
say(" identity frame in H and reachable from every frame in k steps:", prim is not None and key(np.eye(3, dtype=int)) in idx)
np.savetxt(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'results', 'phase5a_frame_matrix.txt'), F, fmt='%d',
           header="FR30 frame substitution matrix F[G',G]; frames (row-major 3x3) in order: " + "; ".join(str(k) for k in Hset))
# the geometric orientation group: chair shape stabilizer in SO(3,Z) is the cyclic coordinate permutations (order 3)
stab = [M for M in SO3Z if {tuple((M @ np.array(u) + (1 - M @ np.ones(3, dtype=int)) // 2)) for u in U3} == set(U3)]
say(f" stabilizer of the chair cube-set in SO(3,Z) (frames giving the same cube set): order {len(stab)}  -> {24 // len(stab)} geometric orientations, {len(Hset)} decorated prototiles")

# ---------------------------------------------------------------- 2. nesting
say("=" * 78); say("2. NESTING T_m subset T_{m+1} AS THE (0,0,0)-CHILD, WITH IDENTICAL LINKS")
def pose_key(G, T): return (key(G), tuple(int(x) for x in T))
tiles = {m: tiles_at_level(FR30, m) for m in range(1, 5)}
for m in range(1, 4):
    Pm = {pose_key(G, T) for G, T, _ in tiles[m]}; Pm1 = {pose_key(G, T) for G, T, _ in tiles[m + 1]}
    sub = Pm <= Pm1
    # the (0,0,0) child op is (I,0): the first-level child (I,0) of the root reproduces exactly T_m
    say(f" level {m}: poses(T_{m}) subset poses(T_{m+1}): {sub}   |T_{m}|={len(Pm)} |T_{m+1}|={len(Pm1)}")
    # panels among T_m's tiles inside T_{m+1} == panels of T_m, with identical links
    owner_m, edges_m = panel_edges(tiles[m]); owner_m1, edges_m1 = panel_edges(tiles[m + 1])
    pos_m = {pose_key(G, T): a for a, (G, T, _) in enumerate(tiles[m])}
    pos_m1 = {pose_key(G, T): a for a, (G, T, _) in enumerate(tiles[m + 1])}
    def panel_sig(tl, edges, pos_filter):
        sig = collections.Counter()
        for a, b, n, ca, cb in edges:
            ka, kb = pose_key(tl[a][0], tl[a][1]), pose_key(tl[b][0], tl[b][1])
            if ka in pos_filter and kb in pos_filter:
                sig[(ka, kb, tuple(int(x) for x in n), ca, cb, q8label(clifford_link(tl[a][0], tl[b][0], n)))] += 1
        return sig
    s_m = panel_sig(tiles[m], edges_m, Pm); s_m1 = panel_sig(tiles[m + 1], edges_m1, Pm)
    say(f"   panels among T_{m}-tiles: in T_{m} {sum(s_m.values())}, in T_{m+1} restricted {sum(s_m1.values())}; identical multisets with identical links: {s_m == s_m1}")

# ---------------------------------------------------------------- 3. rotation covariance of links
say("=" * 78); say("3. LINK RULE IS FRAME-ROTATION COVARIANT: links of sigma^m(t) equal links of T_m for every frame G of t")
def inflate_pose(G, T, m):
    poses = [(G, T)]
    for _ in range(m): poses = [(Gp @ g, 2 * Tp + Gp @ t) for Gp, Tp in poses for g, t in ops]
    base = [np.array([2 * u[0] + 1, 2 * u[1] + 1, 2 * u[2] + 1]) for u in U3]
    return [(Gp, Tp, frozenset(tuple((Gp @ bc + 2 * Tp - 1) // 2) for bc in base)) for Gp, Tp in poses]
ok_all = True
for m in (1, 2):
    ref = tiles[m]; o_ref, e_ref = panel_edges(ref)
    def canon(tl, edges):
        # orientation-free panel list: (min, max, label of C_{min->max}); C_{ba} = C_{ab}^dagger
        out = []
        for a, b, n, _, _ in edges:
            C = clifford_link(tl[a][0], tl[b][0], n)
            if a > b: a, b, C = b, a, C.conj().T
            out.append((a, b, q8label(C)))
        return sorted(out)
    ref_links = canon(ref, e_ref)
    for Gk in Hset:
        G = np.array(Gk).reshape(3, 3)
        rot = inflate_pose(G, np.array([0, 0, 0]), m)   # same enumeration order as the reference
        o_r, e_r = panel_edges(rot)
        rot_links = canon(rot, e_r)
        ok_all &= (rot_links == ref_links)
    say(f" level {m}: for all {len(Hset)} frames G, the panel list and Q8 link labels of sigma^{m}((G,0)) equal those of T_{m}: {ok_all}")

# ---------------------------------------------------------------- 4. degree 24 and boundary tiles
say("=" * 78); say("4. COORDINATION 24, BOUNDARY TILES, SURFACE BOUND")
chair = set(U3); ext = 0
for u in chair:
    for ax in range(3):
        for s in (1, -1):
            w = list(u); w[ax] += s
            if tuple(w) not in chair: ext += 1
say(f" external unit faces of one chair: {ext}  (7 cubes x 6 faces = 42, minus 2 x 9 internal adjacencies)")
for m in range(1, 7):
    t0 = time.time(); tl = tiles_at_level(FR30, m); owner, edges = panel_edges(tl); n = len(tl)
    deg = collections.Counter()
    for a, b, _, _, _ in edges: deg[a] += 1; deg[b] += 1
    N = 2 ** (m + 1)
    cubes_all = set(owner)
    def on_surface(a):
        for c in tl[a][2]:
            for ax in range(3):
                for s in (1, -1):
                    w = list(c); w[ax] += s
                    if tuple(w) not in cubes_all: return True
        return False
    bnd = [a for a in range(n) if deg[a] < 24]
    touch = all(on_surface(a) for a in bnd)
    interior_ok = all(deg[a] == 24 for a in range(n) if not on_surface(a))
    say(f" level {m}: tiles {n}=8^{m}, panels {len(edges)}, max degree {max(deg.values())}, boundary tiles b_m={len(bnd)}  b_m/8^m={len(bnd)/n:.4f}  "
        f"24*4^m={24 * 4 ** m}  b_m<=24*4^m: {len(bnd) <= 24 * 4 ** m}  all boundary tiles touch the surface: {touch}  all non-surface tiles have degree 24: {interior_ok}  ({time.time() - t0:.0f}s)")
    if m >= 5: break   # level 6 is 262144 tiles; b_6 = 23723 is in audit/results/phase5_bulk_bottom_lobpcg.txt

# ---------------------------------------------------------------- 5. recognizability: notch rule and parity
say("=" * 78); say("5. RECOGNIZABILITY: PARITY OF BOUNDING-BOX CORNERS AND THE NOTCH RULE")
for m in range(1, 5):
    tl = tiles_at_level(FR30, m); n = len(tl)
    # central chairs: last child op is the center op, i.e. pose T = 1 mod 2 (all coordinates odd)
    boxes = []
    for G, T, cs in tl:
        arr = np.array(sorted(cs)); lo = arr.min(axis=0); hi = arr.max(axis=0)
        assert (hi - lo == 1).all()
        boxes.append(tuple(int(x) for x in lo))
    par = collections.Counter(tuple(int(x) % 2 for x in b) for b in boxes)
    say(f" level {m}: bounding-box corner parities: {dict(par)}")
    assert set(par) <= {(0, 0, 0), (1, 1, 1)}
    central = [i for i, b in enumerate(boxes) if b[0] % 2 == 1]
    # the notch of chair i: the one cube of its 2x2x2 box not in the chair
    owner = {c: a for a, (_, _, cs) in enumerate(tl) for c in cs}
    notch = {}
    for i, (G, T, cs) in enumerate(tl):
        b = boxes[i]
        box = {(b[0] + e[0], b[1] + e[1], b[2] + e[2]) for e in itertools.product((0, 1), repeat=3)}
        (nc,) = tuple(box - set(cs)); notch[i] = nc
    notch_owner = collections.Counter(notch.values())
    assert max(notch_owner.values()) == 1, "a cube is the notch of two chairs"
    is_notch = set(notch.values())
    cnt = {i: sum(1 for c in cs if c in is_notch) for i, (_, _, cs) in enumerate(tl)}
    cen_counts = collections.Counter(cnt[i] for i in central); out_counts = collections.Counter(cnt[i] for i in range(n) if i not in central)
    say(f"   central chairs: {len(central)} = 8^{m-1}; notch-cube counts of central chairs: {dict(cen_counts)}; of outer chairs: {dict(out_counts)}")
    rule_ok = all(cnt[i] == 7 for i in central) and all(cnt[i] <= 1 for i in range(n) if i not in central)
    # every outer chair's notch is a cube of a central chair, and lies in the same level-1 supertile (same first m-1 child ops)
    # level-1 supertile membership: tiles are enumerated as blocks of 8 consecutive indices (children of one level-(m-1) tile)
    same_super = all(owner[notch[i]] // 8 == i // 8 and (owner[notch[i]] in central) for i in range(n) if i not in central)
    say(f"   notch rule (central <=> 7 notch cubes; outer <= 1): {rule_ok};  every outer notch is a cube of the central chair of its own supertile: {same_super}")
    # supertile centers are = 0 or (2,2,2) mod 4
    cen_mod4 = collections.Counter(tuple((boxes[i][k] + 1) % 4 for k in range(3)) for i in central)
    say(f"   central-chair box centers mod 4: {dict(cen_mod4)}")

# ---------------------------------------------------------------- 6. fixed-point seeds
say("=" * 78); say("6. FIXED-POINT SEEDS")
g0, t0_ = ops[0]
T = np.array([-1, -1, -1])
child = (g0, 2 * T + np.eye(3, dtype=int) @ t0_)
say(f" central child of pose (I,(-1,-1,-1)) is (g,T) = ({key(child[0])}, {tuple(int(x) for x in child[1])}) -> self: {key(child[0]) == key(np.eye(3, dtype=int)) and tuple(child[1]) == (-1, -1, -1)}")
say(" (0,0,0)-child of the root (I,0) is (I,0): the nested T_m exhaust the octant [0,oo)^3 only (box [0,2^(m+1))^3 minus [2^m,2^(m+1))^3)")
for m in (1, 2, 3):
    pts = inflate_pose(np.eye(3, dtype=int), T, m)
    allc = np.array([c for _, _, cs in pts for c in cs]); lo, hi = allc.min(axis=0), allc.max(axis=0)
    say(f"  sigma^{m}(seed) bounding box {tuple(int(x) for x in lo)}..{tuple(int(x) + 1 for x in hi)} (expected [-2^(m-1), 3*2^(m-1)) ), cubes {len(allc)} = 7*8^{m}: {len(allc) == 7 * 8 ** m}")

with open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'results', 'phase5a_frame_substitution.txt'), 'w') as f:
    f.write("\n".join(OUT) + "\n")
