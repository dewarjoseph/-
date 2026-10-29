#!/usr/bin/env python3
"""Phase XIII, the Unique Games comparison: a Chair44 rule's Q8 game, its label-extended graph, and the representation blocks.

The game on the pinned supertile T_L (phase12_unique_games.game): labels s : tiles -> Q8, panel (a, b) with link U demands
s(a) = U s(b).  Its label-extended graph (the graph used by spectral algorithms for unique games, e.g. Kolla 2011) has the
vertices (tile, g), g in Q8, and the edges (b, g) -- (a, U g); with the pinned diagonal 24 its Laplacian is 24 - A_ext.
Since the constraints act by left multiplication, A_ext is the graph's connection in the left-regular representation of Q8,
which splits as 1 + chi_i + chi_j + chi_k + 2 x (spinor).  Hence, exactly,
    spec(24 - A_ext) = spec(trivial) u spec(three Z2 shadows) u spec(quaternion form)        (multiplicities included),
the quaternion form (phase12_independent.operator, 4 real rows per tile) being the spinor block twice.  The Chair44 floor
studied in Phases X-XII is the floor of the faithful (spinor) block; the shadows are the Z2 = F_2 translation games of the
abelian quotient Q8/{+-1} = F_2^2, the instance format of the Unique Games Theorem with s = 2.
Usage: python -u -I audit/phase13_ug_label_extended.py -> audit/results/phase13_ug_label_extended.json"""
import os, sys, json
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); RES = os.path.join(HERE, 'results')
import numpy as np, scipy.sparse as sp
import phase12_independent as I, phase12_unique_games as UG

def chi(q, s, t):
    """the one-dimensional characters of Q8 (trivial on the centre): i -> s, j -> t, k -> s t"""
    w, x, y, z = q
    if abs(w) == 1: return 1
    if abs(x) == 1: return s
    if abs(y) == 1: return t
    return s * t

def blocks(spec, L):
    n, a, b, U, bnd, f, T = UG.game(spec, L)
    rows, cols = [], []
    for x, y, u in zip(a, b, U):
        for g in range(8):
            p, q = 8 * x + UG.MUL[u, g], 8 * y + g; rows += [p, q]; cols += [q, p]
    A = sp.csr_matrix((np.ones(len(rows)), (rows, cols)), shape=(8 * n, 8 * n))
    ext = np.sort(np.linalg.eigvalsh((24 * sp.eye(8 * n) - A).toarray()))
    spin = np.sort(np.linalg.eigvalsh(I.operator(f, T).toarray()))
    Qs = [tuple(int(c) for c in q) for q in UG.Q]; shadows = {}
    for name, (s, t) in {'trivial': (1, 1), 'chi_i': (-1, 1), 'chi_j': (1, -1), 'chi_k': (-1, -1)}.items():
        sg = np.array([chi(Qs[u], s, t) for u in U], float)
        B = sp.csr_matrix((np.r_[sg, sg], (np.r_[a, b], np.r_[b, a])), shape=(n, n))
        shadows[name] = np.sort(np.linalg.eigvalsh((24 * sp.eye(n) - B).toarray()))
    union = np.sort(np.concatenate(list(shadows.values()) + [spin]))
    # the abelian quotient as a translation game over F_2^2: is it exactly satisfiable (a coboundary)?  Spanning-tree check.
    quot = {u: (0 if chi(Qs[u], -1, 1) == 1 else 1, 0 if chi(Qs[u], 1, -1) == 1 else 1) for u in set(U.tolist())}
    lab = [None] * n; adj = [[] for _ in range(n)]
    for x, y, u in zip(a, b, U): adj[x].append((y, quot[u])); adj[y].append((x, quot[u]))
    viol = 0
    for r0 in range(n):
        if lab[r0] is not None: continue
        lab[r0] = (0, 0); st = [r0]
        while st:
            v = st.pop()
            for w, c in adj[v]:
                want = (lab[v][0] ^ c[0], lab[v][1] ^ c[1])
                if lab[w] is None: lab[w] = want; st.append(w)
    for x, y, u in zip(a, b, U):
        c = quot[u]
        if (lab[x][0] ^ lab[y][0], lab[x][1] ^ lab[y][1]) != c: viol += 1
    return {'rule': spec, 'L': L, 'tiles': n, 'panels': int(len(a)), 'label_extended_dim': 8 * n,
            'max_abs_difference_ext_vs_blocks': float(np.abs(ext - union).max()),
            'floors': {k: float(v[0]) for k, v in shadows.items()} | {'spinor (quaternion form)': float(spin[0])},
            'floor_label_extended': float(ext[0]),
            'quotient_F2^2_game_coboundary': viol == 0, 'quotient_tree_section_violated_panels (an upper bound on the minimum)': viol}

if __name__ == '__main__':
    out = []
    for spec in ('1387', 'x539311', '4752'):
        for L in (2, 3):
            rec = blocks(spec, L); out.append(rec); print(rec, flush=True)
    json.dump(out, open(os.path.join(RES, 'phase13_ug_label_extended.json'), 'w'), indent=1)
