"""
Phase 5B / Workstream E, task E3 (spectral consequences): EXACT low moments of the integrated density of states from
the exact 1-star and 2-star type frequencies (audit/results/phase5b_e_star_frequencies.txt, written by
audit/phase5b_e_recursion_correlations.py).

m_k := lim_m (1/8^m) Tr (H^pin_m)^k   (trace over l^2(tiles) x C^2, so m_0 = 2 per tile).
(H^k)_{aa} is a sum over closed walks of length k from tile a; a walk of length k stays within graph distance
floor(k/2) of a, hence within the floor(k/2)-star of a (tiles at graph distance <= r share a cube face chain of
length r, so they lie within Chebyshev distance r of a), and all its matrix elements are determined by the poses in
that star.  Therefore  m_k = sum over star types s of  u(s) * Tr_{C^2} ((H_s^k)_{center})  for k <= 2 (1-stars) and
k <= 4 (2-stars), where H_s = 24 I - A_s is the operator of the star patch (all panels between its tiles).  The
boundary tiles of T_m (whose stars are incomplete) are a vanishing fraction, so the normalised trace converges to this
limit (Theorem 4.3 of the framework also gives the IDS limit).  The moments are exact rationals.  Consistency: m_2 is
computed from both the 1-star and the 2-star frequencies and must agree; m_0 = 2, m_1 = 48.

Run from the repository root:  python3 -u -I audit/phase5b_e_ids_moments.py
Output: audit/results/phase5b_e_ids_moments.txt
"""
import os, sys, ast, time, collections, itertools
from fractions import Fraction
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from independent_clifford_q8_audit import FR30, U3, perm_mat, clifford_link
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
def cubes_of(g, t): return [tuple(int(x) for x in c) for c in (np.einsum('ij,kj->ki', g, LB) + 2 * np.asarray(t)[None, :] - 1) // 2]
def gi(C):
    M = np.rint(np.stack([C.real, C.imag], -1)).astype(np.int64); assert np.allclose(M[..., 0] + 1j * M[..., 1], C); return M

def star_operator(members):
    """H = 24 I - A on the star patch as exact Gaussian-integer (Re, Im) arrays; returns (Re, Im, center index)."""
    poses = [(Gs[f], np.array(t)) for f, t in members]
    center = [i for i, (f, t) in enumerate(members) if f == 0 and tuple(t) == (0, 0, 0)]; assert len(center) == 1
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
    return Re, Im, center[0]
def center_trace_powers(Re, Im, center, kmax):
    """Tr_{C^2} ((H^k)_{center,center}) for k = 0..kmax, exact (Python ints via object arrays)."""
    H = Re.astype(object) + 1j * Im.astype(object) if False else None
    # exact complex-integer arithmetic with two object arrays
    R = Re.astype(object); I = Im.astype(object)
    PR = np.zeros_like(R); PI = np.zeros_like(I)
    for i in range(R.shape[0]): PR[i, i] = 1
    out = []
    for k in range(kmax + 1):
        out.append(int(PR[2*center, 2*center] + PR[2*center+1, 2*center+1])); assert PI[2*center, 2*center] == 0
        PR, PI = PR.dot(R) - PI.dot(I), PR.dot(I) + PI.dot(R)
    return out

t0 = time.time()
lines = open(os.path.join(HERE, 'results', 'phase5b_e_star_frequencies.txt')).read().splitlines()
sec = 0; U1 = []; U2 = []
for ln in lines:
    if ln.startswith('#'): sec += 1; continue
    fr_, mem = ln.split('\t'); mem = ast.literal_eval(mem)
    (U1 if sec == 1 else U2).append((Fraction(fr_), mem))
say(f"loaded {len(U1)} one-star and {len(U2)} two-star types with exact frequencies (sums {sum(u for u, _ in U1)}, {sum(u for u, _ in U2)})")
m1 = [Fraction(0)] * 3
for u, mem in U1:
    Re, Im, c = star_operator(mem); tr = center_trace_powers(Re, Im, c, 2)
    for k in range(3): m1[k] += u * tr[k]
say(f"from 1-stars: m_0 = {m1[0]}, m_1 = {m1[1]}, m_2 = {m1[2]} = {float(m1[2]):.6f}   ({time.time()-t0:.0f}s)")
m2 = [Fraction(0)] * 5; dist_m4 = collections.Counter()
for u, mem in U2:
    Re, Im, c = star_operator(mem); tr = center_trace_powers(Re, Im, c, 4)
    for k in range(5): m2[k] += u * tr[k]
say(f"from 2-stars: m_0 = {m2[0]}, m_1 = {m2[1]}, m_2 = {m2[2]}, m_3 = {m2[3]} = {float(m2[3]):.6f}, m_4 = {m2[4]} = {float(m2[4]):.6f}   ({time.time()-t0:.0f}s)")
say(f"consistency m_2 (1-stars) == m_2 (2-stars): {m1[2] == m2[2]};  m_0 = 2: {m2[0] == 2};  m_1 = 48: {m2[1] == 48}")
# normalised IDS moments (per state): <E^k> = m_k / m_0
E1 = m2[1] / 2; E2 = m2[2] / 2; E3 = m2[3] / 2; E4 = m2[4] / 2
var = E2 - E1 ** 2; mu3 = E3 - 3 * E1 * E2 + 2 * E1 ** 3; mu4 = E4 - 4 * E1 * E3 + 6 * E1 ** 2 * E2 - 3 * E1 ** 4
say(f"IDS moments per state: <E> = {E1}, <E^2> = {E2}, <E^3> = {E3}, <E^4> = {E4}")
say(f"centred: variance {var} = {float(var):.6f} (std {float(var)**0.5:.6f}), third central moment {mu3} = {float(mu3):.4f} (skewness {float(mu3)/float(var)**1.5:.6f}), fourth central moment {mu4} = {float(mu4):.3f} (kurtosis {float(mu4)/float(var)**2:.6f})")
# the level-m finite-size traces for comparison (float, exact in integers really): Tr H^k / 8^m at m = 3, 4, 5
from independent_clifford_q8_audit import tiles_at_level, panel_edges
import scipy.sparse as sps
for m in (3, 4, 5):
    tiles = tiles_at_level(FR30, m); own, edges = panel_edges(tiles); n = len(tiles)
    rows, cols, vals = [], [], []
    for a, b, nv, _, _ in edges:
        C = clifford_link(tiles[a][0], tiles[b][0], nv)
        for r in range(2):
            for cc in range(2): rows += [2*a+r, 2*b+cc]; cols += [2*b+cc, 2*a+r]; vals += [-C[r, cc], -np.conj(C[r, cc])]
    H = (sps.coo_matrix((vals, (rows, cols)), shape=(2*n, 2*n)) + 24 * sps.identity(2*n)).tocsr()
    H2 = H @ H; H3 = H2 @ H; H4 = H3 @ H
    tr = [2 * n, H.diagonal().sum().real, H2.diagonal().sum().real, H3.diagonal().sum().real, H4.diagonal().sum().real]
    say(f"  T_{m}: 8^-m Tr H^k, k=0..4: " + ", ".join(f"{t/8**m:.4f}" for t in tr) + f"   (limits {float(m2[0])}, {float(m2[1])}, {float(m2[2]):.4f}, {float(m2[3]):.4f}, {float(m2[4]):.4f}; pinned boundary rows have the same diagonal 24 but fewer panels, giving O(2^-m) deficits)")
say("What these moments can and cannot say: they are exact spectral invariants of H_omega (moments of the IDS dN), fixed by the"
    " radius-2 pattern frequencies; the support infimum E_bulk is NOT determined by finitely many moments (any finite moment sequence is"
    " compatible with measures whose support starts anywhere below the Chebyshev-Markov bound), so they constrain but do not locate the band edge.")
say(f"total {time.time()-t0:.0f}s")
