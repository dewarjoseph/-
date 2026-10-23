#!/usr/bin/env python3
"""Phase VI: first-principles gauge / quantum audit of the Chair44 Clifford-Q8 construction.

Everything here is rebuilt from the definitions (substitution, panels, link formula); the repository's operator builder is used
only as an independent cross-check.

DEFINITIONS (conventions stated once).
  Tiles a (chairs) with frames M_a in SO(3,Z) (signed permutation, det 1); panels f = (a, b, k) = unit squares shared by tiles a,b
  with normal e_k.  s(v) := sigma.v (Hermitian, unitary, det -1 for a unit vector v).
  Link (repository definition):        C_ab^f = s(M_a^T e_k) s(M_b^T e_k) in Q8,   C_ba^f = (C_ab^f)^dagger.
  Gauge group: G = prod_a SU(2), acting as  C_ab -> g_a C_ab g_b^{-1},  psi_a -> g_a psi_a  (so H -> g H g^dagger).
  Holonomy of a closed walk gamma = (a_0, f_1, a_1, ..., f_m, a_m = a_0):  W_gamma = C_{a_0 a_1}^{f_1} ... C_{a_{m-1} a_0}^{f_m};
           W_gamma -> g_{a_0} W_gamma g_{a_0}^{-1}  (conjugacy class / trace gauge invariant).
  Free (Neumann) connection Laplacian:  L_U = sum_f |psi_a - C_ab psi_b|^2  =  Deg - A_U  (Deg_aa = number of panels of a).
  Pinned operator (Phases V-A..V-E):    H_pin = 24 - A_U  =  L_U + (24 - Deg)   (Dirichlet-type wall on boundary tiles).
  SU(2) lift of a frame: g_hat(M) in SU(2) with g (sigma.v) g^dagger = sigma.(M v)  (defined up to sign).

CHECKS (python -u -I audit/phase6_gauge_audit.py [maxlevel]; results -> audit/results/phase6_gauge_audit.json):
  A  independent operator == repository operator (phase5a_controls.build_H), entrywise
  B  lab-gauge identity  g_hat_a C_ab g_hat_b^{-1} = s(e_k) g_hat_a g_hat_b^{-1} s(e_k)   for every panel (exact)
  C  corner factorization of every fundamental-cycle holonomy (see theorem G2 in deliverables/PHASE6_GAUGE_QM_AUDIT.md)
  D  axis flatness: the subgraph of e_k-panels carries a pure-gauge connection, g_a = i s(M_a^T e_k)
  E  holonomy census on a full fundamental-cycle basis, holonomy group, plaquette census; gauge covariance of all of these
  F  zero-mode dichotomy: lambda_min(L_U) = 0 iff U is pure gauge (FR30, trivial, random pure gauge, axis subgraphs)
  G  spectra and spin-traced transition probabilities under random SU(2) gauge
"""
import os, sys, json, time, itertools, collections, types
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); RES = os.path.join(HERE, 'results')
try:
    import resource  # noqa: F401
except ImportError:
    sys.modules['resource'] = types.SimpleNamespace(getrusage=lambda *a: types.SimpleNamespace(ru_maxrss=0), RUSAGE_SELF=0)
import numpy as np, scipy.sparse as sps, scipy.linalg as sla, scipy.sparse.linalg as spl

SIG = [np.array([[0, 1], [1, 0]], complex), np.array([[0, -1j], [1j, 0]], complex), np.array([[1, 0], [0, -1]], complex)]
I2 = np.eye(2, dtype=complex)
def s(v): return v[0] * SIG[0] + v[1] * SIG[1] + v[2] * SIG[2]
Q8 = {'+1': I2, '-1': -I2}
for k, nm in enumerate('ijk'): Q8['+' + nm] = 1j * SIG[k]; Q8['-' + nm] = -1j * SIG[k]
def q8name(U, tol=1e-9):
    for nm, Q in Q8.items():
        if np.abs(U - Q).max() < tol: return nm
    return None
def qclass(U):
    t = np.trace(U).real
    return '+1' if t > 1.5 else ('-1' if t < -1.5 else ('traceless' if abs(t) < 1e-9 else 'other'))

# ------------------------------------------------------------------ substitution (written from the definition)
FR30 = {'0': (0, 1, 2), (0, 0, 0): (0, 1, 2), (0, 0, 1): (0, 2, 1), (0, 1, 0): (2, 1, 0), (0, 1, 1): (1, 2, 0),
        (1, 0, 0): (1, 0, 2), (1, 0, 1): (0, 1, 2), (1, 1, 0): (2, 0, 1)}
U3 = [v for v in itertools.product((0, 1), repeat=3) if v != (1, 1, 1)]
def P(p):
    M = np.zeros((3, 3), int)
    for i in range(3): M[i, p[i]] = 1
    return M
def tiles(frames, level):
    ops = [(P(frames['0']), np.array([1, 1, 1]))] + [(np.diag([1 - 2 * v[0], 1 - 2 * v[1], 1 - 2 * v[2]]) @ P(frames[v]), 4 * np.array(v)) for v in U3]
    poses = [(np.eye(3, dtype=int), np.zeros(3, dtype=int))]
    for _ in range(level): poses = [(G @ g, 2 * T + G @ t) for G, T in poses for g, t in ops]
    base = [np.array([2 * u[0] + 1, 2 * u[1] + 1, 2 * u[2] + 1]) for u in U3]
    return [(G, frozenset(tuple((G @ bc + 2 * T - 1) // 2) for bc in base)) for G, T in poses]
def panels(tl):
    """list of (a, b, k, cube_a): one entry per unit panel shared by two different tiles (normal +e_k from a to b)."""
    owner = {c: a for a, (_, cs) in enumerate(tl) for c in cs}; out = []
    for c, a in owner.items():
        for k in range(3):
            c2 = list(c); c2[k] += 1; b = owner.get(tuple(c2))
            if b is not None and b != a: out.append((a, b, k, c))
    return out

def link(Ma, Mb, k):
    e = np.zeros(3); e[k] = 1
    return s(Ma.T @ e) @ s(Mb.T @ e)

def su2_lift(M):
    """g in SU(2) with g (sigma.v) g^dagger = sigma.(M v) (unit-quaternion formula); sign fixed by Re(trace) >= 0 when possible."""
    M = np.asarray(M, float); tr = np.trace(M)
    if tr > -1 + 1e-9:
        w = 0.5 * np.sqrt(1 + tr); x = (M[2, 1] - M[1, 2]) / (4 * w); y = (M[0, 2] - M[2, 0]) / (4 * w); z = (M[1, 0] - M[0, 1]) / (4 * w)
    else:                                                          # rotation by pi: w = 0
        w = 0.0; d = np.diag(M); i = int(np.argmax(d)); q = np.zeros(3); q[i] = np.sqrt((1 + d[i]) / 2)
        for j in range(3):
            if j != i: q[j] = (M[i, j] + M[j, i]) / (4 * q[i])
        x, y, z = q
    g = w * I2 - 1j * (x * SIG[0] + y * SIG[1] + z * SIG[2])
    for v in np.eye(3):                                            # verify the defining property
        assert np.abs(g @ s(v) @ g.conj().T - s(M @ v)).max() < 1e-12
    return g

def operator(tl, pn, links, diag):
    n = len(tl); rows, cols, vals = [], [], []
    for (a, b, k, _), C in zip(pn, links):
        for r in range(2):
            for c in range(2):
                rows += [2 * a + r, 2 * b + c]; cols += [2 * b + c, 2 * a + r]; vals += [-C[r, c], -np.conj(C[r, c])]
    for a in range(n):
        for r in range(2): rows.append(2 * a + r); cols.append(2 * a + r); vals.append(diag[a])
    return sps.csr_matrix((vals, (rows, cols)), shape=(2 * n, 2 * n))

# ------------------------------------------------------------------ cycles
def tree_and_cycles(n, pn):
    """BFS spanning tree of the panel multigraph; one fundamental cycle per non-tree panel (parallel panels give 2-cycles)."""
    adj = collections.defaultdict(list)
    for idx, (a, b, k, _) in enumerate(pn): adj[a].append((b, idx)); adj[b].append((a, idx))
    parent = {0: (None, None)}; order = [0]; q = collections.deque([0]); tree = set()
    while q:
        u = q.popleft()
        for v, idx in adj[u]:
            if v not in parent: parent[v] = (u, idx); tree.add(idx); order.append(v); q.append(v)
    assert len(parent) == n, 'panel graph not connected'
    depth = {0: 0}
    for v in order[1:]: depth[v] = depth[parent[v][0]] + 1
    def path_to_root(v):
        out = []
        while parent[v][0] is not None: out.append((v, parent[v][1])); v = parent[v][0]
        return out
    cycles = []
    for idx, (a, b, k, _) in enumerate(pn):
        if idx in tree: continue
        pa, pb = path_to_root(a), path_to_root(b)                  # lists of (vertex, panel to parent)
        sa = {v for v, _ in pa} | {0}; sb_index = {v: i for i, (v, _) in enumerate(pb)}
        # lowest common ancestor
        anc_a = [a] + [parent[v][0] for v, _ in pa]
        lca = next(v for v in anc_a if v in sb_index or v == 0 or v in {w for w, _ in pb} or v == b)
        # walk: a -> (panel idx) -> b -> up to lca -> down to a
        cyc = [(a, idx, b)]
        v = b
        while v != lca:
            u, e = parent[v]; cyc.append((v, e, u)); v = u
        down = []; v = a
        while v != lca:
            u, e = parent[v]; down.append((u, e, v)); v = u
        cyc += down[::-1]
        assert cyc[-1][2] == cyc[0][0] and all(cyc[i][2] == cyc[i + 1][0] for i in range(len(cyc) - 1)), 'not a closed walk'
        cycles.append(cyc)
    return tree, cycles

def oriented_link(pn, links, idx, frm, to):
    a, b, k, _ = pn[idx]
    return links[idx] if (frm, to) == (a, b) else links[idx].conj().T

def holonomy(pn, links, cyc):
    W = I2.copy()
    for frm, idx, to in cyc: W = W @ oriented_link(pn, links, idx, frm, to)
    return W

def corner_form(tl, pn, cyc, glift):
    """theorem G2: W = g_{a0}^{-1} [prod_i kappa_i] ... written as prod over vertices of Ad_{g_a^{-1}}(s(n_in) s(n_out)),
    starting from the base point; returns the product to be compared with W up to the explicit conjugation."""
    m = len(cyc); out = I2.copy()
    axes = [pn[idx][2] for _, idx, _ in cyc]
    e = np.eye(3)
    # W = s(M_{a0}^T n_1) * prod_{i=1}^{m-1} c_{a_i}(n_i, n_{i+1}) * s(M_{a0}^T n_m)   with  c_a(n,n') = s(M_a^T n) s(M_a^T n')
    a0 = cyc[0][0]; M0 = tl[a0][0]
    out = s(M0.T @ e[axes[0]])
    for i in range(m - 1):
        ai = cyc[i][2]; Mi = tl[ai][0]
        out = out @ s(Mi.T @ e[axes[i]]) @ s(Mi.T @ e[axes[i + 1]])
    return out @ s(M0.T @ e[axes[-1]])

# ------------------------------------------------------------------ main audit
def audit_level(level, frames=FR30, seed=0):
    t0 = time.time(); tl = tiles(frames, level); pn = panels(tl); n = len(tl)
    links = [link(tl[a][0], tl[b][0], k) for a, b, k, _ in pn]
    deg = np.zeros(n);
    for a, b, k, _ in pn: deg[a] += 1; deg[b] += 1
    rec = {'level': level, 'tiles': n, 'panels': len(pn), 'max_degree': int(deg.max()), 'boundary_tiles': int((deg < 24).sum())}
    # A: cross-check with the repository builder
    try:
        from independent_clifford_q8_audit import tiles_at_level, panel_edges
        from phase5a_controls import clifford_links, build_H
        tr = tiles_at_level(frames, level); _, er = panel_edges(tr)
        Hr = build_H(len(tr), er, clifford_links(tr, er), np.full(len(tr), 24.0))
        Hm = operator(tl, pn, links, np.full(n, 24.0))
        same_order = all(frozenset(tr[i][2]) == tl[i][1] for i in range(n))
        rec['A_operator_max_abs_diff'] = float(np.abs((Hm - Hr).toarray()).max()) if same_order and n <= 600 else float(abs(Hm - Hr).max())
        rec['A_same_tile_order'] = bool(same_order)
    except Exception as ex: rec['A_error'] = repr(ex)
    # Q8 membership
    rec['links_in_Q8'] = all(q8name(C) is not None for C in links)
    rec['link_census'] = dict(collections.Counter(q8name(C) for C in links))
    # B: lab-gauge identity
    gl = [su2_lift(G) for G, _ in tl]; e = np.eye(3); devB = 0.0
    for (a, b, k, _), C in zip(pn, links):
        lhs = gl[a] @ C @ gl[b].conj().T; rhs = s(e[k]) @ gl[a] @ gl[b].conj().T @ s(e[k]); devB = max(devB, np.abs(lhs - rhs).max())
    rec['B_lab_gauge_max_dev'] = float(devB)
    # E: fundamental cycles
    tree, cycles = tree_and_cycles(n, pn)
    Ws = [holonomy(pn, links, c) for c in cycles]
    rec['cycle_rank'] = len(cycles); rec['cycle_lengths'] = dict(collections.Counter(len(c) for c in cycles))
    rec['E_fundamental_cycle_classes'] = dict(collections.Counter(qclass(W) for W in Ws))
    rec['E_two_cycles_from_parallel_panels'] = dict(collections.Counter(qclass(W) for W, c in zip(Ws, cycles) if len(c) == 2))
    # holonomy group (tree gauge: the non-tree links themselves after gauge fixing generate it)
    gens = {q8name(W) for W in Ws}; grp = {'+1'}; frontier = set(gens)
    while frontier:
        new = set()
        for x in frontier | grp:
            for y in gens:
                z = q8name(Q8[x] @ Q8[y])
                if z not in grp and z not in frontier: new.add(z)
        grp |= frontier; frontier = new
    rec['E_holonomy_group'] = sorted(grp); rec['E_holonomy_group_order'] = len(grp)
    # C: corner factorization on every cycle (exact equality)
    rec['C_corner_max_dev'] = float(max(np.abs(W - corner_form(tl, pn, c, gl)).max() for W, c in zip(Ws, cycles)))
    # D: axis flatness: gauge g_a = i s(M_a^T e_k) trivialises every e_k panel link
    devD = 0.0
    for (a, b, k, _), C in zip(pn, links):
        ga = 1j * s(tl[a][0].T @ e[k]); gb = 1j * s(tl[b][0].T @ e[k]); devD = max(devD, np.abs(ga.conj().T @ C @ gb - I2).max())
        assert abs(np.linalg.det(ga) - 1) < 1e-12
    rec['D_axis_flat_max_dev'] = float(devD)
    # E': gauge covariance: random SU(2) per tile; links change, cycle-holonomy traces do not
    rng = np.random.default_rng(seed)
    def rsu2():
        q = rng.normal(size=4); q /= np.linalg.norm(q); return q[0] * I2 - 1j * (q[1] * SIG[0] + q[2] * SIG[1] + q[3] * SIG[2])
    g = [rsu2() for _ in range(n)]
    links_g = [g[a] @ C @ g[b].conj().T for (a, b, k, _), C in zip(pn, links)]
    Wg = [holonomy(pn, links_g, c) for c in cycles]
    rec['E_gauge_links_changed_max'] = float(max(np.abs(Cg - C).max() for Cg, C in zip(links_g, links)))
    rec['E_gauge_trace_invariance_max_dev'] = float(max(abs(np.trace(A) - np.trace(B)) for A, B in zip(Ws, Wg)))
    rec['E_gauge_conjugation_max_dev'] = float(max(np.abs(g[c[0][0]] @ W @ g[c[0][0]].conj().T - Wgg).max() for W, Wgg, c in zip(Ws, Wg, cycles)))
    # F: zero-mode dichotomy on the free (Neumann) connection Laplacian, levels small enough for dense eigensolves
    if n <= 600:
        def lmin(lk):
            L = operator(tl, pn, lk, deg).toarray(); w = np.linalg.eigvalsh(L); return [float(x) for x in w[:4]]
        pure = [g[a] @ g[b].conj().T for a, b, k, _ in pn]                            # random pure gauge
        rec['F_free_lowest'] = {'fr30_q8': lmin(links), 'trivial': lmin([I2] * len(pn)), 'random_pure_gauge': lmin(pure),
                                'fr30_gauge_transformed': lmin(links_g)}
        for k in range(3):                                                            # single-axis subgraphs (flat, Theorem G3)
            sel = [i for i, p in enumerate(pn) if p[2] == k]; sub = [pn[i] for i in sel]; d2 = np.zeros(n)
            for a, b, _, _ in sub: d2[a] += 1; d2[b] += 1
            L = operator(tl, sub, [links[i] for i in sel], d2).toarray(); w = np.linalg.eigvalsh(L)
            ncomp = sps.csgraph.connected_components(sps.coo_matrix((np.ones(len(sub)), ([p[0] for p in sub], [p[1] for p in sub])), shape=(n, n)), directed=False)[0]
            rec.setdefault('F_axis_subgraph', {})[str(k)] = {'zero_modes': int((w < 1e-10).sum()), 'components': int(ncomp), 'expected_zero_modes': int(2 * ncomp)}
        # G: spectra and spin-traced transition probabilities under the gauge transformation
        H0 = operator(tl, pn, links, np.full(n, 24.0)).toarray(); Hg = operator(tl, pn, links_g, np.full(n, 24.0)).toarray()
        rec['G_spectrum_max_dev'] = float(np.abs(np.linalg.eigvalsh(H0) - np.linalg.eigvalsh(Hg)).max())
        t = 0.7; U0 = sla.expm(-1j * t * H0); Ug = sla.expm(-1j * t * Hg)
        P0 = np.array([[np.sum(np.abs(U0[2*a:2*a+2, 2*b:2*b+2]) ** 2) / 2 for b in range(n)] for a in range(0, n, max(1, n // 32))])
        Pg = np.array([[np.sum(np.abs(Ug[2*a:2*a+2, 2*b:2*b+2]) ** 2) / 2 for b in range(n)] for a in range(0, n, max(1, n // 32))])
        rec['G_transition_prob_max_dev'] = float(np.abs(P0 - Pg).max())
        rec['G_amplitude_max_change'] = float(np.abs(U0 - Ug).max())
    rec['seconds'] = time.time() - t0
    return rec, tl, pn, links

def plaquette_census(tl, pn, links):
    """elementary inter-tile plaquettes: unit squares of the cube lattice whose 4 surrounding cubes are not all in one tile;
    holonomy around the 4 cubes (through the panels between consecutive cubes; panels inside a tile contribute 1)."""
    owner = {c: a for a, (_, cs) in enumerate(tl) for c in cs}; frame = [G for G, _ in tl]
    def L(c, c2, k):                         # link from cube c to its +e_k neighbour c2 (identity if same tile)
        a, b = owner[c], owner[c2]
        return I2 if a == b else link(frame[a], frame[b], k)
    cnt = collections.Counter()
    for c in owner:
        for k1, k2 in ((0, 1), (0, 2), (1, 2)):
            c1 = list(c); c1[k1] += 1; c1 = tuple(c1); c12 = list(c1); c12[k2] += 1; c12 = tuple(c12); c2 = list(c); c2[k2] += 1; c2 = tuple(c2)
            if not all(x in owner for x in (c1, c12, c2)): continue
            ts = {owner[x] for x in (c, c1, c12, c2)}
            if len(ts) == 1: continue
            W = L(c, c1, k1) @ L(c1, c12, k2) @ L(c2, c12, k1).conj().T @ L(c, c2, k2).conj().T
            cnt[qclass(W)] += 1
    return dict(cnt)

def main(maxlevel=3):
    out = {}
    for L in range(1, maxlevel + 1):
        rec, tl, pn, links = audit_level(L)
        rec['plaquette_classes'] = plaquette_census(tl, pn, links)
        out[str(L)] = rec
        print(f"[level {L}] tiles {rec['tiles']} panels {rec['panels']} cycles {rec['cycle_rank']} | A {rec.get('A_operator_max_abs_diff')} | B {rec['B_lab_gauge_max_dev']:.1e} "
              f"| C {rec['C_corner_max_dev']:.1e} | D {rec['D_axis_flat_max_dev']:.1e} | cycles {rec['E_fundamental_cycle_classes']} | group {rec['E_holonomy_group_order']} "
              f"| plaquettes {rec['plaquette_classes']} | F {rec.get('F_free_lowest', {}).get('fr30_q8', [None])[:2]} trivial {rec.get('F_free_lowest', {}).get('trivial', [None])[:2]} ({rec['seconds']:.0f}s)", flush=True)
    json.dump(out, open(os.path.join(RES, 'phase6_gauge_audit.json'), 'w'), indent=1)
    return out

if __name__ == '__main__': main(int(sys.argv[1]) if len(sys.argv) > 1 else 3)
