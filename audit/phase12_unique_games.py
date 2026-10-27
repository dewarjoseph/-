#!/usr/bin/env python3
"""Phase XII, section 15: a Chair44 rule read as a unique game, and the exact relation of its frustration to the spectral floor.

The unique game.  On the tiles of a patch K (here the pinned supertile T_L) the alphabet is Q8 and each panel e = (a, b) carries
the constraint s(a) = U(a->b) s(b), U the Q8 link (phase12_independent.LINK, quaternion convention).  A labelling s : K -> Q8 is
a gauge section; the defect of e is d_e = s(a)^-1 U(a->b) s(b), and e is satisfied iff d_e = 1.  The value of the game is the
largest satisfied fraction of panels.

The relation (Proposition 15.1 of the report).  In the quaternion (realified) form of the operator the links act by left
multiplication, so for a unit quaternion xi the vector psi(v) = s(v) xi has |psi(a) - U psi(b)|^2 = |1 - d_e|^2 = 2 - 2 Re d_e
on every panel (0, 4, 2 for d = 1, -1, traceless) and |psi|^2 = 1 on every tile.  Hence, exactly,
    Y_L = lambda_min(pinned T_L) <= B(s) := [ sum_{e in K} (2 - 2 Re d_e) + b(K) ] / |K|      for every section s,
b(K) the number of boundary panel-ends of K.  The spectral floor of the supertile is at most its weighted frustration density.

Computed here [E, heuristic]: good sections, by spectral rounding of the pinned ground state (the standard unique-games step:
each tile takes the label g whose g xi best matches the eigenvector, xi taken at the heaviest tile) and by seeded random starts,
each followed by local search (every tile in turn takes the label minimising the cost of its panels).  The best value found is an
upper bound on min_s B(s) and a lower bound on the game value; the exact optimum is not computed.
Usage: python -u -I audit/phase12_unique_games.py <L> <spec> ... -> audit/results/phase12_unique_games.jsonl"""
import os, sys, json, time
os.environ.setdefault('OMP_NUM_THREADS', '1')
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); RES = os.path.join(HERE, 'results')
import numpy as np, scipy.sparse.linalg as sla
import phase12_independent as I
OUT = os.path.join(RES, 'phase12_unique_games.jsonl')
Q = np.array(I.Q8, dtype=np.int64)                                     # 8 x 4, (w, x, y, z)
MUL = np.array([[I.QIDX[I.qmul(tuple(Q[i]), tuple(Q[j]))] for j in range(8)] for i in range(8)])
INV = np.array([I.QIDX[(int(Q[i, 0]), int(-Q[i, 1]), int(-Q[i, 2]), int(-Q[i, 3]))] for i in range(8)])
COST = 2 - 2 * Q[:, 0]                                                 # |1 - d|^2: 0 (d = 1), 4 (d = -1), 2 (traceless)

def game(spec, L):
    f, T = I.supertile(I.decoration(spec), L); P = I.Owner(f, T).panels(); a, b, k = P[:, 0], P[:, 1], P[:, 2]
    U = I.LINK[f[a], f[b], k]; n = len(f)
    deg = np.bincount(a, minlength=n) + np.bincount(b, minlength=n)
    return n, a, b, U, int((24 - deg).sum()), f, T

def cost(s, a, b, U): return COST[MUL[MUL[INV[s[a]], U], s[b]]]

def local_search(s, a, b, U, n, rng, sweeps=100):
    inc = [[] for _ in range(n)]
    for e, (x, y) in enumerate(zip(a, b)): inc[x].append(e); inc[y].append(e)
    inc = [np.array(l, dtype=np.int64) for l in inc]
    prev = int(cost(s, a, b, U).sum())
    for _ in range(sweeps):
        for v in rng.permutation(n):
            es = inc[v]; trial = []
            for g in range(8):
                s[v] = g; trial.append(int(cost(s, a[es], b[es], U[es]).sum()))
            s[v] = int(np.argmin(trial))
        tot = int(cost(s, a, b, U).sum())
        if tot >= prev: break
        prev = tot
    return s

def spectral_section(f, T, n):
    """section from the pinned ground state of the quaternion-form operator (phase12_independent.operator, 4 real rows per tile)"""
    H = I.operator(f, T); N = H.shape[0]
    if N <= 4096: w, V = np.linalg.eigh(H.toarray()); lam, x = w[0], V[:, 0]
    else: w, V = sla.eigsh(H, k=1, which='SA', tol=1e-10); lam, x = w[0], V[:, 0]
    psi = x.reshape(n, 4); v0 = int(np.argmax((psi ** 2).sum(1))); xi = psi[v0] / np.linalg.norm(psi[v0])
    gx = np.array([I.qmul(tuple(q), tuple(xi)) for q in Q], dtype=float)  # the 8 quaternions g xi
    return float(lam), np.argmax(psi @ gx.T, axis=1)

def run(spec, L, restarts=6):
    t0 = time.time(); n, a, b, U, bnd, f, T = game(spec, L); rng = np.random.default_rng(0)
    lam, s0 = spectral_section(f, T, n); starts = [('spectral', s0)] + [('random', rng.integers(0, 8, n)) for _ in range(restarts)]
    found = []
    for kind, s in starts:
        s = local_search(s.copy(), a, b, U, n, rng); c = cost(s, a, b, U); found.append((int(c.sum()), kind, c))
    tot, kind, c = min(found, key=lambda t: t[0])
    rec = {'rule': spec, 'L': L, 'tiles': n, 'panels': int(len(a)), 'boundary_panel_ends': bnd, 'Y_L_float': lam,
           'best_start': kind, 'satisfied_fraction': float((c == 0).mean()), 'traceless_defects': int((c == 2).sum()),
           'minus_one_defects': int((c == 4).sum()), 'B_best': (tot + bnd) / n, 'B_interior_per_tile': tot / n,
           'B_by_start': {f'{k}{i}': (t + bnd) / n for i, (t, k, _) in enumerate(found)}, 'seconds': time.time() - t0}
    assert lam <= rec['B_best'] + 1e-9                                  # Proposition 15.1
    with open(OUT, 'a') as fh: fh.write(json.dumps(rec) + '\n')
    print({k: v for k, v in rec.items() if k != 'B_by_start'}, flush=True); return rec

if __name__ == '__main__':
    L = int(sys.argv[1])
    for spec in sys.argv[2:]: run(spec, L)
