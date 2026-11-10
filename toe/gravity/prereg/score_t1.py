"""T1 scorer: rigidity count of tile-wise constant, tangentially continuous (Regge-type) metrics on the chair complex.

Read-only use of the toe mirror: imports chair.py from /workspace/qis-eth/mirror/toe/src with bytecode writing disabled.
Run:  /workspace/qsim-venv/bin/python -I score_t1.py [--smoke]
Definitions (see prereg T1_regge_rigidity.json):
  cells = chair tiles of T_L (tile mode) or unit cubes of the T_L region (cube control);
  metric space M = {g : cells -> Sym(3,R)} with, for every unit face shared by two different cells and normal to axis k,
      g_a[i,j] = g_b[i,j] for all i,j != k  (tangential-tangential continuity);
  N = dim M = sum over the 6 components (i,j) of #connected components of the graph whose edges are the shared faces
      with normal k not in {i,j};  trivial value 6 (global constant metrics);
  gauge space = linearised continuous cell-wise affine deformations u (u affine on every cell, continuous across faces);
  G = dim of their image delta g_a = A_a + A_a^T in M;  Q = N - G (linearised geometric moduli; 0 means all pure gauge);
  N_int = sum over components (i,j) of #graph components containing at least one interior cell (no boundary face).
Ranks: pivot rows found mod p = 2^31-1, then certified over Q: exact Fraction nullspace Z of the pivot rows and an exact
integer check that every row annihilates Z (=> rank over Q equals rank mod p). Uncertified results are flagged."""
import sys, os, json, time, hashlib, argparse
sys.dont_write_bytecode = True
sys.path.insert(0, '/workspace/qis-eth/mirror/toe/src')
os.environ.setdefault('OMP_NUM_THREADS', '2'); os.environ.setdefault('OPENBLAS_NUM_THREADS', '2')
import numpy as np
from fractions import Fraction
from scipy.sparse import coo_matrix
from scipy.sparse.csgraph import connected_components, breadth_first_order
import chair as C

P = 2147483647
COMP = [(0, 0), (1, 1), (2, 2), (0, 1), (0, 2), (1, 2)]
OUT = '/home/box/shared/theory-of-everything/gravity/results/T1_score.json'
CAP_S = 30 * 60
T0 = time.time()


def faces(grid):
    """every unit face between two different cells: (a, b, k, plane coordinate p) with a the lower cell along k"""
    out = []
    for k in range(3):
        A = np.moveaxis(grid, k, 0)
        a, b = A[:-1], A[1:]
        pc = np.broadcast_to(np.arange(1, A.shape[0]).reshape(-1, 1, 1), a.shape)
        m = (a >= 0) & (b >= 0) & (a != b)
        out.append((a[m], b[m], np.full(int(m.sum()), k), pc[m]))
    return [np.concatenate(x).astype(np.int64) for x in zip(*out)]


def boundary_cells(grid):
    g = np.pad(grid, 1, constant_values=-1)
    occ = g >= 0
    bd = set()
    for k in range(3):
        for s in (1, -1):
            nb = np.roll(g, s, axis=k)
            m = occ & (nb < 0)
            bd.update(np.unique(g[m]).tolist())
    return bd


def components(n, a, b):
    if len(a) == 0:
        return n, np.arange(n)
    M = coo_matrix((np.ones(len(a)), (a, b)), shape=(n, n))
    return connected_components(M, directed=False)


def rank_mod_p_pivots(R):
    """R: int64 array (rows x cols), entries reduced mod P. Returns indices of original rows forming a basis mod P."""
    R = R.copy() % P
    nr, nc = R.shape
    used = np.zeros(nr, dtype=bool)
    piv = []
    for j in range(nc):
        cand = np.nonzero((R[:, j] != 0) & ~used)[0]
        if len(cand) == 0:
            continue
        r = cand[0]
        used[r] = True
        piv.append(int(r))
        inv = pow(int(R[r, j]), P - 2, P)
        R[r] = (R[r] * inv) % P
        others = np.nonzero((R[:, j] != 0) & (np.arange(nr) != r))[0]
        if len(others):
            f = R[others, j].copy()
            # (R_o - f * R_r) mod P, done in two halves to stay inside int64
            R[others] = (R[others] - (f[:, None] * R[r][None, :]) % P) % P
    return piv


def nullspace_exact(S, nc):
    """exact rational nullspace of integer rows S (list of lists) -> integer basis vectors (list of lists)"""
    M = [[Fraction(int(x)) for x in row] for row in S]
    pivcols, r = [], 0
    for j in range(nc):
        pr = next((i for i in range(r, len(M)) if M[i][j] != 0), None)
        if pr is None:
            continue
        M[r], M[pr] = M[pr], M[r]
        pv = M[r][j]
        M[r] = [x / pv for x in M[r]]
        for i in range(len(M)):
            if i != r and M[i][j] != 0:
                f = M[i][j]
                M[i] = [x - f * y for x, y in zip(M[i], M[r])]
        pivcols.append(j)
        r += 1
    free = [j for j in range(nc) if j not in pivcols]
    basis = []
    for fj in free:
        v = [Fraction(0)] * nc
        v[fj] = Fraction(1)
        for i, pj in enumerate(pivcols):
            v[pj] = -M[i][fj]
        den = 1
        for x in v:
            den = den * x.denominator // np.gcd(den, x.denominator)
        basis.append([int(x * den) for x in v])
    return basis, len(pivcols)


def certified_rank(R_int):
    """R_int: object or int64 integer matrix. Returns (rank, integer nullspace basis Z (nc x k), certified flag)."""
    R_int = np.asarray(R_int, dtype=object)
    nr, nc = R_int.shape
    if nr == 0:
        return 0, [[1 if i == j else 0 for i in range(nc)] for j in range(nc)], True
    Rm = np.array([[int(x) % P for x in row] for row in R_int], dtype=np.int64)
    piv = rank_mod_p_pivots(Rm)
    S = [list(R_int[i]) for i in piv]
    Z, rq = nullspace_exact(S, nc)
    cert = (rq == len(piv))
    if cert and Z:
        Zm = np.array(Z, dtype=object).T
        cert = bool(np.all(R_int.dot(Zm) == 0))
    return len(piv), Z, cert


def analyse(grid, label):
    n = int(grid.max()) + 1
    a, b, k, pc = faces(grid)
    bd = boundary_cells(grid)
    interior = np.array([i not in bd for i in range(n)])
    res = {'cells': n, 'shared_faces': int(len(a)), 'interior_cells': int(interior.sum()), 'components': {}}
    labs = {}
    N = N_int = 0
    for (i, j) in COMP:
        m = (k != i) & (k != j)
        nc_, lab = components(n, a[m], b[m])
        labs[(i, j)] = lab
        sizes = np.bincount(lab)
        has_int = np.bincount(lab, weights=interior.astype(float)) > 0
        N += int(nc_)
        N_int += int(has_int.sum())
        res['components'][f'g{i}{j}'] = {'n': int(nc_), 'with_interior_cell': int(has_int.sum()),
                                          'largest_sizes': sorted(sizes.tolist(), reverse=True)[:5]}
    res['N'] = N
    res['N_int'] = N_int
    # ---- gauge: continuous cell-wise affine scalar functions f; grad on cell a = (alpha_j[lab_jj(a)])_j
    off = [0, 0, 0]
    cs = [int(labs[(j, j)].max()) + 1 for j in range(3)]
    off[1], off[2] = cs[0], cs[0] + cs[1]
    c = sum(cs)
    col = lambda j, cell: off[j] + labs[(j, j)][cell]
    # unique continuity relations (a, b, k, p): beta_b - beta_a = p (alpha_k(a) - alpha_k(b))
    E = np.unique(np.stack([a, b, k, pc], 1), axis=0)
    ncc, _ = components(n, E[:, 0], E[:, 1])
    assert ncc == 1, 'cell graph disconnected'
    adj = coo_matrix((np.arange(1, len(E) + 1), (E[:, 0], E[:, 1])), shape=(n, n)).tocsr()
    order, pred = breadth_first_order(adj + adj.T, 0, directed=False, return_predecessors=True)
    # edge lookup for tree edges
    key = {}
    for idx, (x, y, kk, p) in enumerate(E.tolist()):
        key.setdefault((x, y), idx); key.setdefault((y, x), idx)
    def wvec(idx):
        x, y, kk, p = E[idx].tolist()
        v = {}
        v[col(kk, x)] = v.get(col(kk, x), 0) + p
        v[col(kk, y)] = v.get(col(kk, y), 0) - p
        return x, y, v          # beta_y - beta_x = v . alpha
    pot = np.zeros((n, c), dtype=np.int64)
    tree = set()
    for node in order[1:]:
        par = pred[node]
        idx = key[(par, node)]
        tree.add(idx)
        x, y, v = wvec(idx)
        s = 1 if (x, y) == (par, node) else -1
        pot[node] = pot[par]
        for cc, val in v.items():
            pot[node, cc] += s * val
    rows = []
    for idx in range(len(E)):
        if idx in tree:
            continue
        x, y, v = wvec(idx)
        r = -(pot[y] - pot[x])
        for cc, val in v.items():
            r[cc] += val
        if np.any(r):
            rows.append(r)
    K = np.unique(np.array(rows, dtype=np.int64), axis=0) if rows else np.zeros((0, c), dtype=np.int64)
    rK, Z, certK = certified_rank(K)
    dimW = len(Z)
    res.update({'alpha_vars': c, 'cycle_constraint_rows_unique': int(len(K)), 'rank_K': rK, 'dim_affine_scalar_grad': dimW,
                'certified_K': certK})
    # ---- gauge image: variables y_m in R^dimW (m = 0,1,2), alpha^(m) = Z y_m
    Zc = np.array(Z, dtype=object).T if dimW else np.zeros((c, 0), dtype=object)   # c x dimW
    pats = set()
    for (i, j) in COMP:
        li, lj = labs[(i, i)], labs[(j, j)]
        for t in set(zip(li.tolist(), lj.tolist())):
            pats.add((i, j) + t)
    Mrows = []
    for (i, j, ci, cj) in sorted(pats):
        r = np.zeros(3 * dimW, dtype=object)
        if i == j:
            r[i * dimW:(i + 1) * dimW] += 2 * Zc[off[i] + ci]
        else:
            r[i * dimW:(i + 1) * dimW] += Zc[off[j] + cj]
            r[j * dimW:(j + 1) * dimW] += Zc[off[i] + ci]
        Mrows.append(r)
    Mg = np.array(Mrows, dtype=object) if Mrows else np.zeros((0, 3 * dimW), dtype=object)
    G, _, certG = certified_rank(Mg)
    res.update({'G': G, 'certified_G': certG, 'Q': N - G})
    res['seconds_elapsed_total'] = round(time.time() - T0, 1)
    print(label, json.dumps({x: res[x] for x in ('cells', 'N', 'N_int', 'G', 'Q', 'certified_K', 'certified_G')}), flush=True)
    return res


def tile_grid(rule, L):
    G_, T_ = C.supertile(rule, L)
    return C.owner_grid(G_, T_, L)


def cube_grid(L):
    g = tile_grid(C.FR30, L)
    out = -np.ones_like(g)
    occ = g >= 0
    out[occ] = np.arange(int(occ.sum()))
    return out


def partition_key(grid):
    n = int(grid.max()) + 1
    flat = grid.ravel()
    order = np.argsort(flat, kind='stable')
    cells = np.split(order[flat[order] >= 0], np.cumsum(np.bincount(flat[flat >= 0], minlength=n))[:-1])
    return hashlib.sha256(repr(sorted(tuple(sorted(c.tolist())) for c in cells)).encode()).hexdigest()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--smoke', action='store_true', help='L = 0 only, prints, writes nothing')
    args = ap.parse_args()
    rules = {'FR30': C.FR30, '1387': C.proper_rule(1387)}
    if args.smoke:
        analyse(tile_grid(C.FR30, 0), 'smoke tile L0')
        analyse(cube_grid(0), 'smoke cube L0')
        return
    prereg = '/home/box/shared/theory-of-everything/gravity/prereg/T1_regge_rigidity.json'
    out = {'prereg': prereg, 'prereg_sha256': hashlib.sha256(open(prereg, 'rb').read()).hexdigest(),
           'scorer_sha256': hashlib.sha256(open(__file__, 'rb').read()).hexdigest(),
           'started': time.strftime('%Y-%m-%d %H:%M:%S %Z'), 'rules': {k: [list(p) for p in v] for k, v in rules.items()},
           'cube_control': {}, 'tiles': {}, 'not_run': []}
    for L in (1, 2, 3):
        if time.time() - T0 > CAP_S:
            out['not_run'].append(f'cube L{L}'); continue
        n = 2 ** (L + 1)
        r = analyse(cube_grid(L), f'cube L{L}')
        r['V1_expected_N'] = 3 * n + 3 * n * n
        out['cube_control'][str(L)] = r
    for L in (1, 2, 3, 4, 5):
        for name, rule in rules.items():
            if time.time() - T0 > CAP_S:
                out['not_run'].append(f'{name} L{L}'); continue
            g = tile_grid(rule, L)
            r = analyse(g, f'{name} L{L}')
            r['partition_sha256'] = partition_key(g)
            out['tiles'].setdefault(str(L), {})[name] = r
    # ---------------- verdicts (exactly as frozen in the prereg)
    v = {}
    cc = out['cube_control']
    v1_ok = len(cc) == 3 and all(cc[s]['N'] == cc[s]['V1_expected_N'] for s in cc)
    v['V1'] = 'pass' if v1_ok else ('fail' if len(cc) == 3 else 'not run')
    tl = out['tiles']
    full = all(str(L) in tl and len(tl[str(L)]) == 2 for L in (1, 2, 3, 4, 5))
    allr = [tl[s][nm] for s in tl for nm in tl[s]]
    cert_all = all(r['certified_K'] and r['certified_G'] for r in allr) and all(r['certified_K'] and r['certified_G'] for r in cc.values())
    def hv(ok):
        if not v1_ok:
            return 'invalid (V1 failed or not run)'
        return ('pass' if ok else 'fail') if full else ('pass on run levels; incomplete' if ok else 'fail')
    v['H1'] = hv(all(r['N'] == 6 for r in allr))
    v['H1b'] = hv(all(tl[s][nm]['N_int'] == 6 for s in tl if int(s) >= 2 for nm in tl[s]))
    v['H2'] = hv(all(tl[s]['FR30'][q] == tl[s]['1387'][q] for s in tl if len(tl[s]) == 2
                     for q in ('partition_sha256', 'N', 'N_int', 'G', 'Q')))
    v['H3'] = hv(all(r['Q'] == 0 for r in allr))
    v['all_ranks_certified_over_Q'] = cert_all
    out['verdicts'] = v
    out['finished'] = time.strftime('%Y-%m-%d %H:%M:%S %Z')
    out['seconds'] = round(time.time() - T0, 1)
    os.makedirs(os.path.dirname(OUT), exist_ok=True)
    json.dump(out, open(OUT, 'w'), indent=1)
    print(json.dumps(v, indent=1))


if __name__ == '__main__':
    main()
