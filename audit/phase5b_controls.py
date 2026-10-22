#!/usr/bin/env python3
"""Phase V-B, Workstream C: interventions that separate hierarchical organisation from flux and local geometry.

All systems live on the same chair geometry (level-L supertile, 8^L chairs, pinned operator 24 I - A, Q8 Clifford links),
so the tile graph, the coordination and the link rule are identical; only the FRAME FIELD differs.  Interventions:

  fr30            the FR30 substitution (deterministic, self-similar at every scale)
  dec<i>          another admissible deterministic substitution (census index i; same hierarchy type, different rule)
  iid<seed>       'independent-rule hierarchy': every parent tile draws its own admissible decoration (one of the 6561)
                  independently at every inflation step.  Local statistics are those of a random admissible rule; there is
                  NO self-similarity (the rule changes from parent to parent), but the block structure (8 children per
                  parent, octant frames with the parity constraint) is kept.
  coarse<seed>    FR30 rule at depths 1..L-1 (all inflation steps but the last), independent random rule at the last
                  step: the coarse hierarchy is FR30's, the finest-scale frames are random.
  fine<seed>      independent random rule at the first inflation step(s) down to depth L-1, FR30 rule at the last step:
                  the finest-scale (level-1 block) structure is FR30's, the coarse arrangement is random.
  shuffle<seed>   FR30 permutation parts randomly re-assigned among octant positions of equal parity, per parent (the
                  position-dependent sign matrices are kept, so admissibility holds): same multiset of local rotations as
                  FR30 in every parent, random spatial arrangement, no self-similarity.
  flip<seed,p>    FR30 with a fraction p of tiles' frames replaced by an independent admissible-parity frame (local defects).

For each system: level-4 (and level-3) pinned bottom with residual, the level-4 class fractions, the Phase V-B predictor
set (audit/phase5b_sweep.predictors), and the residual against the flux baseline fitted on the census (coefficients read
from audit/results/phase5b_sweep_analysis.json if present, else the Phase V-A periodic fit).  Everything printed is
computed in this run.  Usage: python3 -u -I audit/phase5b_controls.py run <system> [...] ; ... table
"""
import os, sys, time, json, itertools
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
RES = os.path.join(HERE, 'results')
import numpy as np
from independent_clifford_q8_audit import FR30, U3, perm_mat, panel_edges
from phase5a_controls import clifford_links, build_H, degrees, EVEN, ODD
import phase5b_sweep as sw

def ops_of(dec):
    ops = [(perm_mat(dec['0']), np.array([1, 1, 1]))]
    for v in U3:
        Ds = np.diag([1 - 2 * v[0], 1 - 2 * v[1], 1 - 2 * v[2]]); ops.append((Ds @ perm_mat(dec[v]), 4 * np.array(v)))
    return ops
BASE = [np.array([2 * u[0] + 1, 2 * u[1] + 1, 2 * u[2] + 1]) for u in U3]
FR30_OPS = ops_of(FR30)

def random_dec(rng): return sw.decoration(int(rng.integers(sw.NDEC)))

def inflate_tiles(level, rule):
    """rule(depth, parent_index, rng-free) -> list of 8 child ops; depth 1 is the first inflation step."""
    poses = [(np.eye(3, dtype=int), np.zeros(3, dtype=int))]
    for depth in range(1, level + 1):
        new = []
        for pi, (G, T) in enumerate(poses):
            for g, t in rule(depth, pi): new.append((G @ g, 2 * T + G @ t))
        poses = new
    tiles = [(G, T, frozenset(tuple((G @ bc + 2 * T - 1) // 2) for bc in BASE)) for G, T in poses]
    return tiles

def system_tiles(name, level):
    if name == 'fr30': return inflate_tiles(level, lambda d, p: FR30_OPS), {}
    if name.startswith('dec'):
        ops = ops_of(sw.decoration(int(name[3:]))); return inflate_tiles(level, lambda d, p: ops), {'census_index': int(name[3:])}
    if name.startswith('iid'):
        rng = np.random.default_rng(int(name[3:])); return inflate_tiles(level, lambda d, p: ops_of(random_dec(rng))), {'seed': int(name[3:])}
    if name.startswith('coarse'):
        rng = np.random.default_rng(int(name[6:]))
        return inflate_tiles(level, lambda d, p: FR30_OPS if d < level else ops_of(random_dec(rng))), {'seed': int(name[6:])}
    if name.startswith('fine'):
        rng = np.random.default_rng(int(name[4:]))
        return inflate_tiles(level, lambda d, p: ops_of(random_dec(rng)) if d < level else FR30_OPS), {'seed': int(name[4:])}
    if name.startswith('shuffle'):
        # per parent: keep the centre frame and the position-dependent sign matrices D_s(v); randomly permute the FR30
        # permutation parts pi_v among the even-|v| octants and among the odd-|v| octants (admissibility preserved, so the
        # local rule stays inside the 6561-decoration space; the multiset of FR30 rotations per parent is unchanged).
        rng = np.random.default_rng(int(name[7:]))
        ev = [v for v in U3 if sum(v) % 2 == 0]; od = [v for v in U3 if sum(v) % 2 == 1]
        def rule(d, p):
            dec = {'0': FR30['0']}
            for grp in (ev, od):
                perm = rng.permutation(len(grp))
                for k, v in enumerate(grp): dec[v] = FR30[grp[perm[k]]]
            return ops_of(dec)
        return inflate_tiles(level, rule), {'seed': int(name[7:])}
    if name.startswith('flip'):
        seed, p = name[4:].split(','); rng = np.random.default_rng(int(seed)); p = float(p)
        tiles = inflate_tiles(level, lambda d, q: FR30_OPS); out = []
        for G, T, cs in tiles:
            if rng.random() < p:
                # replace the frame by G times a random admissible-parity rotation about the tile's own axes (keeps the cube set:
                # the cube set of a chair is invariant only under its 3-element stabilizer, so use that: cyclic axis permutations)
                cyc = [(0, 1, 2), (1, 2, 0), (2, 0, 1)][rng.integers(1, 3)]
                out.append((G @ perm_mat(cyc), T, cs))
            else: out.append((G, T, cs))
        return out, {'seed': int(seed), 'p': p}
    raise ValueError(name)

def analyse(name, level):
    t0 = time.time(); tiles, meta = system_tiles(name, level)
    cubes = [c for _, _, cs in tiles for c in cs]; assert len(set(cubes)) == len(cubes) == 7 * len(tiles), 'overlapping tiles'
    for G, _, _ in tiles: assert round(np.linalg.det(G)) == 1 and (G.T @ G == np.eye(3, dtype=int)).all()
    pred = sw.predictors(tiles, level)
    _, edges = panel_edges(tiles); deg = degrees(len(tiles), edges); assert deg.max() == 24
    links = clifford_links(tiles, edges); H = build_H(len(tiles), edges, links, np.full(len(tiles), 24.0))
    import scipy.linalg as sla
    if level <= 3:
        w, V = sla.eigh(H.toarray(), subset_by_index=(0, 3), driver='evr'); how = 'dense eigh'
        HV = H @ V; lam = np.real(np.einsum('ij,ij->j', V.conj(), HV)); res = np.linalg.norm(HV - V * lam, axis=0)
    else:
        from phase5a_scaling_controls import eig_lobpcg
        lam, V, res, _ = eig_lobpcg(H, 2, extra=2, tol=1e-7); how = 'lobpcg(block=4, tol=1e-7)'
    psi = V[:, 0]; p = np.abs(psi[0::2]) ** 2 + np.abs(psi[1::2]) ** 2; p /= p.sum()
    a = np.array([e[0] for e in edges]); b = np.array([e[1] for e in edges]); anc = lambda x: x // 8 ** (level - 1)
    it = np.unique(np.concatenate([a[anc(a) != anc(b)], b[anc(a) != anc(b)]]))
    rec = {'system': name, 'level': level, 'meta': meta, 'n': len(tiles), 'lambda': [float(x) for x in lam[:4]], 'residual': float(max(res[:2])),
           'solver': how, 'ipr_n': float((p ** 2).sum() * len(tiles)), 'interface1_weight': float(p[it].sum()), 'interface1_fraction': len(it) / len(tiles),
           'boundary_weight': float(p[deg < 24].sum()), 'pred': pred, 'seconds': time.time() - t0}
    print(f"[{name} L{level}] lambda={lam[0]:.6f} res={max(res[:2]):.1e} f_m1={pred['f_m1']:.4f} f_trl={pred['f_trl']:.4f} enr1_trl={pred['enr1_trl']:.3f} "
          f"cv_m1={pred['cv_m1']:.3f} IPR*n={rec['ipr_n']:.2f} w_int1={rec['interface1_weight']:.3f} [{rec['interface1_fraction']:.3f}] ({time.time()-t0:.0f}s)", flush=True)
    return rec

def run(names, levels=(3, 4)):
    path = os.path.join(RES, 'phase5b_controls.jsonl')
    with open(path, 'a') as f:
        for name in names:
            for L in levels:
                rec = analyse(name, L); f.write(json.dumps(rec) + '\n'); f.flush()

def table():
    recs = [json.loads(l) for l in open(os.path.join(RES, 'phase5b_controls.jsonl'))]
    fits = {L: json.load(open(os.path.join(RES, f'phase5b_sweep_fit_L{L}.json'))) for L in (3, 4) if os.path.exists(os.path.join(RES, f'phase5b_sweep_fit_L{L}.json'))}
    lines = []
    P = lambda s='': (print(s), lines.append(s))
    P("PHASE V-B, WORKSTREAM C: INTERVENTIONS ON THE FRAME FIELD (same chair geometry, coordination 24, Q8 rule, pinned operator)")
    P("Fixed in every row: tile graph (8^L chairs of the level-L supertile), panel multiset, link rule, pinned diagonal.  Changed: the frame field as described in the module docstring.")
    for L, fit in fits.items(): P(f"flux baseline from the census (level {L}, n={fit['n']}): Y ~ {fit['c0']:.3f} + {fit['c_trl']:.3f} f_trl + {fit['c_m1']:.3f} f_m1 (rms {fit['rms']:.3f}, CV R^2 {fit['cv_r2']:.3f})")
    for L in sorted({r['level'] for r in recs}):
        P(); P(f"--- level {L} ---")
        P(f"{'system':<14} {'lambda_min':>10} {'res':>8} | {'f_nontriv':>9} {'f_trl':>7} {'f_m1':>7} | {'E_fit':>7} {'resid':>7} | {'enr1_trl':>8} {'enr1_m1':>7} {'cv_m1':>6} {'Cp_m1m1':>7} | {'IPR*n':>7} {'w_int1':>6} {'bw':>6}")
        for r in [r for r in recs if r['level'] == L]:
            pr = r['pred']; fit = fits.get(L); ef = (fit['c0'] + fit['c_trl'] * pr['f_trl'] + fit['c_m1'] * pr['f_m1']) if fit else float('nan')
            P(f"{r['system']:<14} {r['lambda'][0]:10.5f} {r['residual']:8.1e} | {pr['f_nontriv']:9.4f} {pr['f_trl']:7.4f} {pr['f_m1']:7.4f} | {ef:7.3f} {r['lambda'][0]-ef:+7.3f} | "
              f"{pr['enr1_trl']:8.3f} {pr['enr1_m1']:7.3f} {pr['cv_m1']:6.3f} {pr['Cp_m1_m1']:7.3f} | {r['ipr_n']:7.2f} {r['interface1_weight']:6.3f} {r['boundary_weight']:6.3f}")
    with open(os.path.join(RES, 'phase5b_controls.txt'), 'w') as f: f.write('\n'.join(lines) + '\n')

if __name__ == '__main__':
    os.environ.setdefault('OMP_NUM_THREADS', '1')
    if sys.argv[1] == 'run': run(sys.argv[2:])
    elif sys.argv[1] == 'table': table()
