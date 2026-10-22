"""
Phase 5B / Workstream E, task E3 (spectral consequences): EXACT low moments of the integrated density of states from
the exact collared-type frequencies.

m_k := lim_m 8^-m Tr (H^pin_m)^k   (trace over l^2(tiles) x C^2, so m_0 = 2 per tile).
(H^k)_{aa} is a sum over closed walks a -> b -> ... -> a of length k.  For k <= 3 every tile visited is a or a panel
neighbour of a, and the matrix elements needed are the panels among these tiles: all determined by the 1-star of a
(Chebyshev radius 1: a neighbour owns a cube face-adjacent to a cube of a).  For k = 4 the walk a-b-c-d-a visits a tile
c that is a neighbour of a neighbour b; since b's 7 cubes lie in a 2x2x2 box, every cube of b is within Chebyshev
distance 2 of a and every cube of c within distance 3: c lies in the 3-star of a (Chebyshev radius 3; graph distance
2 does NOT imply Chebyshev distance 2).  So
   m_k = sum_s u_1(s) Tr_{C^2}((H_s^k)_{centre})  for k <= 3,      m_4 = sum_s u_3(s) Tr_{C^2}((H_s^4)_{centre}),
with H_s = 24 I - A_s the operator of the star patch (all panels among its tiles; the centre's walks never leave it).
The 3-star types are V_3 = Phi_3(V_2) (closure lemma: the 3-star of a child lies in sigma(2-star of the parent)), with
frequencies u_3 = Phi_3 u_2 / 8.  All moments are exact rationals; m_0 = 2 and m_1 = 48 are consistency checks, and
m_2, m_3 are recomputed from u_3 and must agree with the 1-star values.
Inputs: audit/results/phase5b_e_star_frequencies.txt (from audit/phase5b_e_recursion_correlations.py).
Run from the repository root:  python3 -u -I audit/phase5b_e_ids_moments.py
Output: audit/results/phase5b_e_ids_moments.txt
"""
import os, sys, ast, time, collections, itertools
from fractions import Fraction
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from independent_clifford_q8_audit import FR30, U3, perm_mat, clifford_link, tiles_at_level, panel_edges
import scipy.sparse as sps
OUT = []
def say(*a):
    s = " ".join(str(x) for x in a); print(s, flush=True); OUT.append(s)
    with open(os.path.join(HERE, 'results', 'phase5b_e_ids_moments.txt'), 'w') as f: f.write("\n".join(OUT) + "\n")
ops = [(perm_mat(FR30['0']), np.array([1, 1, 1]))] + [(np.diag([1 - 2 * v[0], 1 - 2 * v[1], 1 - 2 * v[2]]) @ perm_mat(FR30[v]), 4 * np.array(v)) for v in U3]
GOPS = np.array([g for g, t in ops]); I3 = np.eye(3, dtype=int)
def key(M): return tuple(int(x) for x in np.asarray(M).ravel())
Gs = [I3.copy()]; gidx = {key(I3): 0}; fr = [I3]
while fr:
    new = []
    for M in fr:
        for g in GOPS:
            P = M @ g
            if key(P) not in gidx: gidx[key(P)] = len(Gs); Gs.append(P); new.append(P)
    fr = new
assert len(Gs) == 24
LB = np.array([[2 * u[0] + 1, 2 * u[1] + 1, 2 * u[2] + 1] for u in U3])
def cubes_of(g, t, odd=LB): return [tuple(int(x) for x in c) for c in (np.einsum('ij,kj->ki', g, odd) + 2 * np.asarray(t)[None, :] - 1) // 2]
def gi(C):
    M = np.rint(np.stack([C.real, C.imag], -1)).astype(np.int64); assert np.allclose(M[..., 0] + 1j * M[..., 1], C); return M
L3 = [l for l in itertools.product(range(-3, 5), repeat=3) if l != (4, 4, 4)]; assert len(L3) == 511
L3ODD = 2 * np.array(L3) + 1

def star_operator(poses, center):
    own = {}
    for a, (g, t) in enumerate(poses):
        for c in cubes_of(g, t): assert c not in own; own[c] = a
    n = len(poses); Re = np.zeros((2 * n, 2 * n), np.int64); Im = np.zeros((2 * n, 2 * n), np.int64)
    for i in range(2 * n): Re[i, i] = 24
    for c, a in own.items():
        for ax in range(3):
            c2 = (c[0] + (ax == 0), c[1] + (ax == 1), c[2] + (ax == 2)); b = own.get(c2)
            if b is None or b == a: continue
            nv = np.zeros(3, int); nv[ax] = 1; C = gi(clifford_link(poses[a][0], poses[b][0], nv))
            Re[2*a:2*a+2, 2*b:2*b+2] -= C[..., 0]; Im[2*a:2*a+2, 2*b:2*b+2] -= C[..., 1]
            Re[2*b:2*b+2, 2*a:2*a+2] -= C[..., 0].T; Im[2*b:2*b+2, 2*a:2*a+2] += C[..., 1].T
    assert (Re == Re.T).all() and (Im == -Im.T).all()
    return Re, Im
def center_trace_powers(Re, Im, center, kmax):
    """Tr_{C^2}((H^k)_{centre}) for k = 0..kmax, exactly: only the two centre rows of H^k are propagated (row vectors
    times H), with Python integers."""
    R = Re.astype(object); I = Im.astype(object); n = R.shape[0]
    rowsR = np.zeros((2, n), dtype=object); rowsI = np.zeros((2, n), dtype=object)
    for i in range(2): rowsR[i, 2 * center + i] = 1
    for i in range(n):
        for j in range(2): rowsR[j, i] = int(rowsR[j, i]); rowsI[j, i] = 0
    out = []
    for k in range(kmax + 1):
        tr = int(rowsR[0, 2 * center] + rowsR[1, 2 * center + 1]); assert rowsI[0, 2 * center] == 0 and rowsI[1, 2 * center + 1] == 0
        out.append(tr)
        rowsR, rowsI = rowsR.dot(R) - rowsI.dot(I), rowsR.dot(I) + rowsI.dot(R)
    return out
def members_to_poses(mem):
    poses = [(Gs[f], np.array(t)) for f, t in mem]
    center = [i for i, (f, t) in enumerate(mem) if f == 0 and tuple(t) == (0, 0, 0)]; assert len(center) == 1
    return poses, center[0]
def star_key(poses, own, center, odd):
    g0, t0 = poses[center]; mem = set()
    for c in cubes_of(g0, t0, odd):
        o = own.get(c)
        if o is None: return None
        mem.add(o)
    return frozenset((gidx[key(g0.T @ poses[b][0])], tuple(int(x) for x in g0.T @ (poses[b][1] - t0))) for b in mem)
def Phi3(mem):
    poses, center = members_to_poses(mem)
    fine = [(g @ gg, 2 * t + g @ tt) for g, t in poses for gg, tt in ops]; own = {}
    for a, (g, t) in enumerate(fine):
        for c in cubes_of(g, t): own[c] = a
    out = [star_key(fine, own, 8 * center + c, L3ODD) for c in range(8)]; assert None not in out, "closure lemma (radius 3) violated"
    return out

t0 = time.time()
lines = open(os.path.join(HERE, 'results', 'phase5b_e_star_frequencies.txt')).read().splitlines()
sec = 0; U1 = []; U2 = []
for ln in lines:
    if ln.startswith('#'): sec += 1; continue
    fr_, mem = ln.split('\t'); mem = ast.literal_eval(mem)
    (U1 if sec == 1 else U2).append((Fraction(fr_), mem))
say(f"loaded {len(U1)} one-star and {len(U2)} two-star types with exact frequencies (sums {sum(u for u, _ in U1)}, {sum(u for u, _ in U2)})")
m1 = [Fraction(0)] * 4
for u, mem in U1:
    poses, c = members_to_poses(mem); Re, Im = star_operator(poses, c); tr = center_trace_powers(Re, Im, c, 3)
    for k in range(4): m1[k] += u * tr[k]
say(f"from the 72 one-star types: m_0 = {m1[0]}, m_1 = {m1[1]}, m_2 = {m1[2]} = {float(m1[2]):.6f}, m_3 = {m1[3]} = {float(m1[3]):.6f}   ({time.time()-t0:.0f}s)")
# 3-star types and frequencies
U3 = collections.defaultdict(Fraction)
for u, mem in U2:
    for kk in Phi3(mem): U3[kk] += u / 8
say(f"3-star types V_3 = Phi_3(V_2): {len(U3)} types (Chebyshev radius 3, 511 positions), sizes {min(len(k) for k in U3)}..{max(len(k) for k in U3)} tiles; u_3 sum {sum(U3.values())}, max denominator {max(x.denominator for x in U3.values())}   ({time.time()-t0:.0f}s)")
m3 = [Fraction(0)] * 5
for kk, u in U3.items():
    mem = sorted(kk); poses, c = members_to_poses(mem); Re, Im = star_operator(poses, c); tr = center_trace_powers(Re, Im, c, 4)
    for k in range(5): m3[k] += u * tr[k]
say(f"from the 3-star types: m_0 = {m3[0]}, m_1 = {m3[1]}, m_2 = {m3[2]}, m_3 = {m3[3]}, m_4 = {m3[4]} = {float(m3[4]):.6f}   ({time.time()-t0:.0f}s)")
say(f"consistency: m_0 = 2: {m3[0] == 2}; m_1 = 48: {m3[1] == 48}; m_2 (1-stars) == m_2 (3-stars): {m1[2] == m3[2]}; m_3 (1-stars) == m_3 (3-stars): {m1[3] == m3[3]}")
E = [m3[k] / 2 for k in range(5)]
var = E[2] - E[1] ** 2; mu3 = E[3] - 3 * E[1] * E[2] + 2 * E[1] ** 3; mu4 = E[4] - 4 * E[1] * E[3] + 6 * E[1] ** 2 * E[2] - 3 * E[1] ** 4
say(f"IDS moments per state (dN has total mass 1 per spinor-tile dimension): <E> = {E[1]}, <E^2> = {E[2]}, <E^3> = {E[3]}, <E^4> = {E[4]}")
say(f"centred: variance {var} = {float(var):.6f} (std {float(var)**0.5:.6f}); 3rd central moment {mu3} = {float(mu3):.4f} (skewness {float(mu3)/float(var)**1.5:.6f}); 4th central moment {mu4} = {float(mu4):.3f} (kurtosis {float(mu4)/float(var)**2:.6f})")
# same walk counts, trivial connection (all links = 1): moments of the trivial-connection operator 24 - A^triv from the same u_1
mt = [Fraction(0)] * 4
for u, mem in U1:
    poses, c = members_to_poses(mem); Re, Im = star_operator(poses, c)
    Rt = Re.copy(); It = np.zeros_like(Im)
    # rebuild with identity links: off-diagonal 2x2 blocks become -(multiplicity) * I
    n = len(poses); own = {}
    for a, (g, t) in enumerate(poses):
        for cc in cubes_of(g, t): own[cc] = a
    Rt = np.zeros_like(Re)
    for i in range(2 * n): Rt[i, i] = 24
    for cc, a in own.items():
        for ax in range(3):
            c2 = (cc[0] + (ax == 0), cc[1] + (ax == 1), cc[2] + (ax == 2)); b = own.get(c2)
            if b is None or b == a: continue
            for r in range(2): Rt[2*a+r, 2*b+r] -= 1; Rt[2*b+r, 2*a+r] -= 1
    tr = center_trace_powers(Rt, It, c, 3)
    for k in range(4): mt[k] += u * tr[k]
say(f"trivial connection (same tiling, all links 1; framework 3.4 shows its E_bulk = 0) from the same u_1: m_2^triv = {mt[2]}, m_3^triv = {mt[3]}; per state <E^2>-<E>^2 = {mt[2]/2 - 576} = sum_b mult(a,b)^2 (Clifford: {var}), 3rd central moment {mt[3]/2 - 3*24*mt[2]/2 + 2*24**3} (Clifford: {mu3})")
# finite-size traces at levels 3-5 for comparison (float, from the sparse operator)
for m in (3, 4, 5):
    tiles = tiles_at_level(FR30, m); own, edges = panel_edges(tiles); n = len(tiles)
    rows, cols, vals = [], [], []
    for a, b, nv, _, _ in edges:
        C = clifford_link(tiles[a][0], tiles[b][0], nv)
        for r in range(2):
            for cc in range(2): rows += [2*a+r, 2*b+cc]; cols += [2*b+cc, 2*a+r]; vals += [-C[r, cc], -np.conj(C[r, cc])]
    H = (sps.coo_matrix((vals, (rows, cols)), shape=(2*n, 2*n)) + 24 * sps.identity(2*n)).tocsr()
    P = sps.identity(2 * n, format='csr', dtype=complex); tr = []
    for k in range(5): tr.append(P.diagonal().sum().real); P = P @ H
    say(f"  T_{m} (pinned): 8^-m Tr H^k, k=0..4: " + ", ".join(f"{t/8**m:.4f}" for t in tr) + f"   (limits {float(m3[0])}, {float(m3[1])}, {float(m3[2]):.4f}, {float(m3[3]):.4f}, {float(m3[4]):.4f}; boundary tiles lack panels, giving O(2^-m) deficits)")
say("Interpretation: these are exact spectral invariants of H_omega (moments of the hull IDS), fixed by the radius-<=3 pattern frequencies; "
    "the support infimum E_bulk is NOT determined by finitely many moments (a finite moment sequence is compatible with measures whose support "
    "extends down to any point allowed by the Chebyshev-Markov inequalities), so they constrain the IDS but do not locate the band edge.")
say(f"total {time.time()-t0:.0f}s")
