#!/usr/bin/env python3
"""Phase V-A, Task D1: spectral edge versus flux fractions and spatial organization of frustration,
for APERIODIC (substitution) decorations of the chair tiling.

Question. The periodic census (audit/phase5a_periodic_control.py, Task B2a) found that over 44539 periodic Q8
decorations of the Lambda_7 chair crystal the band bottom is fitted by
    E_fit(f) = -1.904 + 14.303 f_traceless + 30.696 f_(-1)      (rms 0.53),
that no flux-matched periodic decoration exceeds 8.18, and that FR30 (E_bulk <= 8.770) lies 4.5 rms above the fit.
Here the same comparison is made for substitution decorations of the chair: FR30 and parity-admissible random
decorations (same RNG and admissibility rule as audit/phase5a_scaling_controls.random_decoration, so seeds 1-3 are
the decorations already used in Task C1).  For each decoration we compute, with code in this file,
  * the level-5 inter-tile plaquette class fractions f_nontriv, f_traceless, f_(-1)  (own vectorised enumeration,
    cross-checked against the FR30 values 60 = 26/3/31 at level 1 and the level-5 class counts of
    audit/results/phase4_type_substitution_proof.txt);
  * the pinned ground-state energy E0 = lambda_min(24 I - A) at levels 4 and 5 (LOBPCG, residuals reported);
  * spatial-organization statistics of the frustration that are NOT determined by the fractions:
      O1  CV(-1)      coefficient of variation over tiles of the number of (-1)-plaquettes touching the tile;
      O2  enr1(-1)    enrichment of (-1)-plaquettes on the top-level (depth-1) supertile interface, i.e.
                      P(plaquette straddles depth-1 boundary | class -1) / P(straddles depth-1 boundary);
      O3  enr1(trl)   the same for traceless plaquettes;
      O4  pair(-1)    nearest-neighbour clustering of frustration: P(a (-1)-plaquette shares a tile with another
                      (-1)-plaquette) relative to the value expected for the same count placed uniformly
                      (computed as mean number of (-1) plaquettes among the plaquettes touching the same tiles,
                      divided by the global (-1) fraction);
  * the ground-state tile participation IPR*n and its depth-1 interface weight at level 5.
Then: residual r = E0(L5) - E_fit(f) for every decoration, and the rank correlation of r with O1-O4.

Everything printed is computed in this run.  Usage:
   python3 -u -I audit/phase5a_flux_vs_edge.py run <name> [<name> ...]     (name: fr30 | randdecN)
   python3 -u -I audit/phase5a_flux_vs_edge.py table
Results: audit/results/phase5a_flux_vs_edge_<name>.json and audit/results/phase5a_flux_vs_edge.txt
"""
import os, sys, time, json, resource
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
RES = os.path.join(HERE, 'results')
import numpy as np
from independent_clifford_q8_audit import FR30, U3, tiles_at_level, panel_edges
from phase5a_controls import clifford_links, build_H, degrees, EVEN, ODD
from phase5a_scaling_controls import random_decoration, eig_lobpcg, eig_dense

# periodic-census regression (Task B2a, audit/results/phase5a_periodic_control_T.txt)
FIT = (-1.904, 14.303, 30.696)
def e_fit(f_trl, f_m1): return FIT[0] + FIT[1] * f_trl + FIT[2] * f_m1

# ---------------------------------------------------------------- Q8 as integer codes
# code: 0 = +1, 1 = -1, 2+2k = +i sigma_k, 3+2k = -i sigma_k   (k = 0,1,2);  class: 0 -> {+1}, 1 -> {-1}, >=2 -> traceless
SIG = [np.array([[0, 1], [1, 0]], complex), np.array([[0, -1j], [1j, 0]], complex), np.array([[1, 0], [0, -1]], complex)]
Q8M = [np.eye(2, dtype=complex), -np.eye(2, dtype=complex)] + [s * 1j * SIG[k] for k in range(3) for s in (1, -1)]
def _mul_table():
    T = np.zeros((8, 8), int)
    for a in range(8):
        for b in range(8):
            P = Q8M[a] @ Q8M[b]; hits = [c for c in range(8) if np.allclose(P, Q8M[c])]
            assert len(hits) == 1; T[a, b] = hits[0]
    return T
MUL = _mul_table()

def link_codes(ua, ub):
    """Codes of (sigma.ua)(sigma.ub) = (ua.ub) I + i (ua x ub).sigma for arrays of signed unit vectors (m,3)."""
    dot = np.einsum('ij,ij->i', ua, ub); cr = np.cross(ua, ub)
    ax = np.argmax(np.abs(cr), axis=1); sgn = cr[np.arange(len(cr)), ax]
    code = np.where(dot == 1, 0, np.where(dot == -1, 1, 2 + 2 * ax + (sgn < 0)))
    return code.astype(int)

def _selfcheck_codes():
    rng = np.random.default_rng(0)
    for _ in range(200):
        ua = np.zeros(3, int); ub = np.zeros(3, int)
        ua[rng.integers(3)] = rng.choice([-1, 1]); ub[rng.integers(3)] = rng.choice([-1, 1])
        C = sum(ua[m] * SIG[m] for m in range(3)) @ sum(ub[m] * SIG[m] for m in range(3))
        c = link_codes(ua[None], ub[None])[0]; assert np.allclose(C, Q8M[c])
_selfcheck_codes()

# ---------------------------------------------------------------- plaquettes
def plaquettes(tiles, level):
    """All lattice-edge plaquettes with four present cubes.  Returns owners (m,4) in cyclic order and holonomy codes."""
    N = 2 ** (level + 1)
    G = np.array([t[0] for t in tiles]); n = len(tiles)
    grid = -np.ones((N, N, N), int)
    for a, (_, _, cs) in enumerate(tiles):
        for c in cs: grid[c] = a
    own_all, code_all = [], []
    for d in range(3):
        a_, b_ = [x for x in range(3) if x != d]
        P = np.stack(np.meshgrid(np.arange(N + 1), np.arange(N + 1), np.arange(N + 1), indexing='ij'), -1).reshape(-1, 3)
        ea = np.zeros(3, int); ea[a_] = 1; eb = np.zeros(3, int); eb[b_] = 1
        # cyclic order around the edge: (0,0) -> (1,0) -> (1,1) -> (0,1) in (s_a, s_b); the four cubes are P - s_a e_a - s_b e_b
        corners = [P, P - ea, P - ea - eb, P - eb]
        ok = np.ones(len(P), bool)
        for c in corners: ok &= ((c >= 0) & (c < N)).all(axis=1)
        corners = [c[ok] for c in corners]
        owners = np.stack([grid[c[:, 0], c[:, 1], c[:, 2]] for c in corners], 1)
        present = (owners >= 0).all(axis=1); owners = owners[present]; corners = [c[present] for c in corners]
        hol = np.zeros(len(owners), int)
        # panels: (c0,c1) normal a, (c1,c2) normal b, (c2,c3) normal a, (c3,c0) normal b
        for (i, j, ax) in ((0, 1, a_), (1, 2, b_), (2, 3, a_), (3, 0, b_)):
            nvec = np.zeros(3, int); nvec[ax] = 1
            oa, ob = owners[:, i], owners[:, j]
            ua = np.einsum('ikj,k->ij', G[oa], nvec); ub = np.einsum('ikj,k->ij', G[ob], nvec)   # M^T n
            lc = link_codes(ua, ub); lc = np.where(oa == ob, 0, lc)
            hol = MUL[hol, lc]
        own_all.append(owners); code_all.append(hol)
    owners = np.concatenate(own_all); hol = np.concatenate(code_all)
    inter = ~((owners == owners[:, :1]).all(axis=1))
    return owners[inter], hol[inter]

def classes(hol):
    return np.where(hol == 0, 0, np.where(hol == 1, 1, 2))   # 0:+1  1:-1  2:traceless

def flux_fractions(hol):
    cl = classes(hol); m = len(hol)
    return {'N': int(m), 'n_plus': int((cl == 0).sum()), 'n_minus': int((cl == 1).sum()), 'n_traceless': int((cl == 2).sum()),
            'f_nontriv': float((cl != 0).mean()), 'f_traceless': float((cl == 2).mean()), 'f_minus': float((cl == 1).mean())}

def organization(owners, hol, n, level):
    cl = classes(hol); m = len(hol)
    anc1 = owners // 8 ** (level - 1)
    straddle1 = ~((anc1 == anc1[:, :1]).all(axis=1))
    p_all = straddle1.mean()
    out = {'frac_straddle_depth1_all': float(p_all)}
    for name, k in (('minus', 1), ('traceless', 2)):
        sel = cl == k
        out[f'enr1_{name}'] = float(straddle1[sel].mean() / p_all) if sel.any() else float('nan')
    # per-tile counts of (-1) plaquettes (each distinct touching tile counted once per plaquette)
    cnt = np.zeros(n, int); sel = cl == 1
    for col in range(4):
        pass
    # distinct owners per plaquette
    o = np.sort(owners[sel], axis=1)
    distinct = np.ones_like(o, bool); distinct[:, 1:] = o[:, 1:] != o[:, :-1]
    np.add.at(cnt, o[distinct], 1)
    out['cv_minus'] = float(cnt.std() / cnt.mean()) if cnt.mean() > 0 else float('nan')
    out['mean_minus_per_tile'] = float(cnt.mean())
    # nearest-neighbour clustering: for each (-1) plaquette, the mean (-1)-count of the tiles it touches, minus itself,
    # divided by the global mean per tile times the same normalisation for all plaquettes
    oa = np.sort(owners, axis=1); da = np.ones_like(oa, bool); da[:, 1:] = oa[:, 1:] != oa[:, :-1]
    touch_sum = (cnt[oa] * da).sum(axis=1); ntouch = da.sum(axis=1)
    own_m = np.where(sel, 1, 0)
    neigh_minus = (touch_sum - own_m * ntouch) / ntouch          # mean number of OTHER (-1) plaquettes per touched tile
    out['pair_minus'] = float(neigh_minus[sel].mean() / neigh_minus.mean()) if sel.any() else float('nan')
    return out

# ---------------------------------------------------------------- decorations
def decoration(name):
    if name == 'fr30': return FR30, {'seed': None}
    if name.startswith('randdec'):
        seed = int(name[7:]); dec, draws = random_decoration(seed); return dec, {'seed': seed, 'draws': draws}
    raise ValueError(name)

def interface_depth1_tiles(level, edges):
    a = np.array([e[0] for e in edges]); b = np.array([e[1] for e in edges])
    anc = lambda x: x // 8 ** (level - 1)
    s = anc(a) != anc(b); return np.unique(np.concatenate([a[s], b[s]]))

def run_one(name, levels=(4, 5), flux_level=5):
    t0 = time.time(); dec, meta = decoration(name)
    rec = {'name': name, 'decoration': {str(k): list(v) for k, v in dec.items()}, **meta, 'levels': {}}
    # flux + organisation at flux_level (and a check at level 1 for FR30)
    tiles = tiles_at_level(dec, flux_level); n = len(tiles)
    owners, hol = plaquettes(tiles, flux_level)
    rec['flux'] = flux_fractions(hol); rec['flux']['level'] = flux_level
    rec['organization'] = organization(owners, hol, n, flux_level)
    rec['E_fit'] = e_fit(rec['flux']['f_traceless'], rec['flux']['f_minus'])
    print(f"[{name}] level-{flux_level} inter-tile plaquettes {rec['flux']['N']}: +1 {rec['flux']['n_plus']}, -1 {rec['flux']['n_minus']}, "
          f"traceless {rec['flux']['n_traceless']}; f_nontriv={rec['flux']['f_nontriv']:.4f} f_trl={rec['flux']['f_traceless']:.4f} "
          f"f_-1={rec['flux']['f_minus']:.4f}; E_fit={rec['E_fit']:.3f}; org={ {k: round(v, 4) for k, v in rec['organization'].items()} }  ({time.time()-t0:.0f}s)", flush=True)
    for L in levels:
        t1 = time.time()
        tl = tiles if L == flux_level else tiles_at_level(dec, L)
        _, edges = panel_edges(tl); deg = degrees(len(tl), edges); assert deg.max() == 24
        links = clifford_links(tl, edges); H = build_H(len(tl), edges, links, np.full(len(tl), 24.0))
        if L <= 3: lam, V, res = eig_dense(H, 2); how = 'dense'
        else: lam, V, res, _ = eig_lobpcg(H, 2, extra=2, tol=1e-7); how = 'lobpcg(block=4, tol=1e-7, seed=0)'
        psi = V[:, 0]; p = np.abs(psi[0::2]) ** 2 + np.abs(psi[1::2]) ** 2; p /= p.sum()
        ipr = float((p ** 2).sum()); it = interface_depth1_tiles(L, edges)
        rec['levels'][str(L)] = {'n': len(tl), 'lambda': [float(x) for x in lam], 'residuals': [float(x) for x in res], 'solver': how,
                                 'ipr_n': ipr * len(tl), 'interface1_weight': float(p[it].sum()), 'interface1_fraction': len(it) / len(tl),
                                 'seconds': time.time() - t1}
        print(f"[{name}] L{L} n={len(tl)}: lambda={lam[0]:.6f} (pair {lam[1]:.6f}) res={max(res):.1e} IPR*n={ipr*len(tl):.3f} "
              f"interface1 weight {p[it].sum():.3f} [frac {len(it)/len(tl):.3f}]  ({time.time()-t1:.0f}s, rss {resource.getrusage(resource.RUSAGE_SELF).ru_maxrss/1e6:.2f} GB)", flush=True)
    rec['seconds'] = time.time() - t0
    with open(os.path.join(RES, f'phase5a_flux_vs_edge_{name}.json'), 'w') as f: json.dump(rec, f, indent=1)
    return rec

def selfcheck():
    """FR30 plaquette classes at levels 1-3 against the stored recursion/enumerator values."""
    expect = {1: (60, 26, 3, 31), 2: (792, 385, 42, 365), 3: (7728, 3945, 530, 3253)}
    for L, (N, p, m, t) in expect.items():
        owners, hol = plaquettes(tiles_at_level(FR30, L), L); f = flux_fractions(hol)
        got = (f['N'], f['n_plus'], f['n_minus'], f['n_traceless'])
        print(f"selfcheck FR30 level {L}: inter-tile plaquettes (N, +1, -1, traceless) = {got}, expected {(N, p, m, t)}: {'OK' if got == (N, p, m, t) else 'MISMATCH'}")
        assert got == (N, p, m, t)

def spearman(x, y):
    from scipy.stats import spearmanr, pearsonr
    r, p = spearmanr(x, y); r2, p2 = pearsonr(x, y); return float(r), float(p), float(r2), float(p2)

def table():
    recs = []
    for fn in sorted(os.listdir(RES)):
        if fn.startswith('phase5a_flux_vs_edge_') and fn.endswith('.json'): recs.append(json.load(open(os.path.join(RES, fn))))
    recs.sort(key=lambda r: (r['name'] != 'fr30', r.get('seed') or 0))
    lines = []
    P = lambda s='': (print(s), lines.append(s))
    P("PHASE V-A, TASK D1: pinned spectral edge of substitution (aperiodic) chair decorations versus flux fractions and the spatial organisation of frustration")
    P("All numbers computed by audit/phase5a_flux_vs_edge.py in this run.  E_fit = periodic-census regression -1.904 + 14.303 f_trl + 30.696 f_-1 (Task B2a).")
    P("Organisation statistics at level 5 (see module docstring): CV(-1), enr1(-1), enr1(trl), pair(-1).  r = E0(L5) - E_fit.")
    P()
    P(f"{'decoration':<12} {'f_nontriv':>9} {'f_trl':>7} {'f_-1':>7} | {'E0 L4':>9} {'E0 L5':>9} {'res':>8} | {'E_fit':>7} {'r':>7} | {'CV(-1)':>7} {'enr1(-1)':>8} {'enr1(trl)':>9} {'pair(-1)':>8} | {'IPR*n L5':>8} {'w_int1':>7}")
    rows = []
    for r in recs:
        f = r['flux']; o = r['organization']; L4 = r['levels'].get('4'); L5 = r['levels'].get('5')
        if L5 is None: continue
        rr = L5['lambda'][0] - r['E_fit']
        rows.append((r['name'], f, o, L4, L5, r['E_fit'], rr))
        P(f"{r['name']:<12} {f['f_nontriv']:9.4f} {f['f_traceless']:7.4f} {f['f_minus']:7.4f} | {L4['lambda'][0] if L4 else float('nan'):9.5f} {L5['lambda'][0]:9.5f} {max(L5['residuals']):8.1e} | "
          f"{r['E_fit']:7.3f} {rr:+7.3f} | {o['cv_minus']:7.3f} {o['enr1_minus']:8.3f} {o['enr1_traceless']:9.3f} {o['pair_minus']:8.3f} | {L5['ipr_n']:8.3f} {L5['interface1_weight']:7.3f}")
    P()
    fr = [x for x in rows if x[0] == 'fr30']; others = [x for x in rows if x[0] != 'fr30']
    if fr and others:
        fr = fr[0]
        rs = np.array([x[6] for x in others]); e5 = np.array([x[4]['lambda'][0] for x in others])
        P(f"FR30: E0(L5) = {fr[4]['lambda'][0]:.5f}, E_fit = {fr[5]:.3f}, residual {fr[6]:+.3f} (periodic census rms 0.532)")
        P(f"random substitution decorations (n={len(others)}): E0(L5) range [{e5.min():.3f}, {e5.max():.3f}], residual r range [{rs.min():+.3f}, {rs.max():+.3f}], mean {rs.mean():+.3f}, sd {rs.std(ddof=1):.3f}")
        P(f"number of random decorations with E0(L5) > FR30's E0(L5): {(e5 > fr[4]['lambda'][0]).sum()};  with residual > FR30's: {(rs > fr[6]).sum()}")
        # flux-matched subset
        fm = [x for x in others if abs(x[1]['f_nontriv'] - fr[1]['f_nontriv']) < 0.03 and abs(x[1]['f_traceless'] - fr[1]['f_traceless']) < 0.04 and abs(x[1]['f_minus'] - fr[1]['f_minus']) < 0.04]
        P(f"random decorations matching all three FR30 fractions within (0.03, 0.04, 0.04): {len(fm)}" + (f"; their E0(L5): {[round(x[4]['lambda'][0], 4) for x in fm]}" if fm else ''))
        allrows = rows
        for key, label in (('cv_minus', 'CV(-1)'), ('enr1_minus', 'enr1(-1)'), ('enr1_traceless', 'enr1(trl)'), ('pair_minus', 'pair(-1)')):
            xs = np.array([x[2][key] for x in allrows]); ys = np.array([x[6] for x in allrows]); zs = np.array([x[4]['lambda'][0] for x in allrows])
            if np.isnan(xs).any(): continue
            sr, sp, pr, pp = spearman(xs, ys); sr2, sp2, _, _ = spearman(xs, zs)
            P(f"  {label:<10} vs residual r: Spearman {sr:+.3f} (p={sp:.3f}), Pearson {pr:+.3f} (p={pp:.3f});  vs E0(L5): Spearman {sr2:+.3f} (p={sp2:.3f});  FR30 value {fr[2][key]:.3f}, rank among {len(allrows)}: {int((xs > fr[2][key]).sum()) + 1}")
        fx = np.array([[x[1]['f_traceless'], x[1]['f_minus']] for x in allrows]); zs = np.array([x[4]['lambda'][0] for x in allrows])
        A = np.c_[np.ones(len(fx)), fx]; coef, *_ = np.linalg.lstsq(A, zs, rcond=None); resid = zs - A @ coef
        P(f"  own least squares over the substitution decorations: E0(L5) ~ {coef[0]:.3f} + {coef[1]:.3f} f_trl + {coef[2]:.3f} f_-1, rms {np.sqrt((resid**2).mean()):.3f} (sd E0 {zs.std():.3f}); FR30 residual to THIS fit {resid[[x[0] for x in allrows].index('fr30')]:+.3f}")
    with open(os.path.join(RES, 'phase5a_flux_vs_edge.txt'), 'w') as f: f.write('\n'.join(lines) + '\n')

if __name__ == '__main__':
    os.environ.setdefault('OMP_NUM_THREADS', '1')
    if sys.argv[1] == 'selfcheck': selfcheck()
    elif sys.argv[1] == 'run':
        for name in sys.argv[2:]: run_one(name)
    elif sys.argv[1] == 'table': table()
