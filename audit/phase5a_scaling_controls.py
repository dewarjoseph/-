#!/usr/bin/env python3
"""
Phase 5a / task C1: level-5 participation scaling of the pinned ground state for FR30 and all matched controls.

Operator (identical to audit/phase5_bulk_bottom_lobpcg.py and audit/phase5a_controls.py): Hilbert space l^2(tiles) x C^2,
  (A psi)_a = sum over shared unit panels f=(a,b) of C_ab psi_b, C_ba = C_ab^dagger, panels between the same pair of
  tiles summed with multiplicity; H_pin = 24 I - A on the chair geometries (bulk coordination 24);
  unit-cube geometry: bulk coordination 6, pinned diagonal 6.
Systems (one process each; run sequentially):
  fr30          FR30 chair, Clifford Q8 links C_ab = (sigma.M_a^T n_f)(sigma.M_b^T n_f)         [reference]
  cube          unit-cube block substitution with the FR30-type decoration ((1,1,1) -> (0,2,1)), Clifford links, pinned 6
  randdec1/2/3  chair substitution with a random parity-admissible decoration (np.random.default_rng(seed), seed 1,2,3):
                frames M_v = D_s(v) P(pi_v), pi_v even for even-weight corner v and for the centre, odd for odd-weight v
                (det M_v = +1), redrawn if equal to FR30; Clifford links; permutation tables recorded
  stripped      FR30 graph, each FR30 link replaced by its V4-class representative with + sign (+1 or +i sigma_k) in the
                edge-list orientation a->b (panel normal = +axis), C_ba = C_ab^dagger
  randq8        FR30 graph, i.i.d. uniform Q8 links, np.random.default_rng(11).integers(0, 8, |E|) in edge-list order
  trivial       FR30 graph, all links I_2 (no flux)
Solvers: level 3 (dim 1024): dense scipy.linalg.eigh (driver evr, subset_by_index=(0,3)); levels 4 and 5: matrix-free LOBPCG
  (block k+4 = 8 at level 4, k+2 = 6 at level 5), diagonal preconditioner, seed 0, tol 1e-7, eigenvalues recomputed as
  Rayleigh quotients; residuals ||H psi - lambda psi||_2 reported for every eigenpair.  The level-4 LOBPCG eigenpairs are
  cross-checked against dense eigh (evr, subset, F-ordered copy, ~1.2 GB) in the separate pass 'dense4' (it is a separate pass
  because the dim-8192 tridiagonalisation takes tens of minutes on the shared, fully loaded machine).
Ground-state diagnostics (pair-averaged tile density p_a = |psi_a1|^2 + |psi_a2|^2, sum_a p_a = 1, averaged over the two
  returned Kramers vectors): IPR = sum p_a^2, IPR*n; box counting S2(d) = sum over the 8^d depth-d children (child index =
  tile_index // 8^(level-d), tiles_at_level / cube_tiles are depth-first) of (weight in child)^2 and the effective number of
  occupied children 1/S2(d); interface tiles at depth d = tiles incident to a shared panel joining two different depth-d
  children, their weight and tile fraction; boundary weight = weight on tiles with deg < bulk coordination.
Run from the repository root (OMP_NUM_THREADS=1):
  python3 -u -I audit/phase5a_scaling_controls.py <system> [maxlevel=5]
  python3 -u -I audit/phase5a_scaling_controls.py table
  python3 -u -I audit/phase5a_scaling_controls.py all [maxlevel]      (runs every system as a subprocess, then table)
  python3 -u -I audit/phase5a_scaling_controls.py dense4 <system> | dense4all [systems]   (dense level-4 cross-check, then table)
Outputs: audit/results/phase5a_scaling_controls_<system>.txt/.json; table -> audit/results/phase5a_scaling_controls.txt/.json
"""
import os, sys, time, json, warnings, collections, resource, subprocess
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
RES = os.path.join(HERE, 'results')
import numpy as np, scipy.sparse as sps, scipy.sparse.linalg as spl, scipy.linalg as sla
from independent_clifford_q8_audit import FR30, U3, tiles_at_level, panel_edges, check_tiling, q8label
from phase5a_controls import (chair, cube_tiles, clifford_links, build_H, degrees, edge_arrays, Q8, I2, EVEN, ODD, V8,
                              tile_density, conv)

SYSTEMS = ['fr30', 'cube', 'randdec1', 'randdec2', 'randdec3', 'stripped', 'randq8', 'trivial']
EXTRA = ['randdec4', 'randdec5', 'randdec6']     # supplementary decorations (not in the task list), only tabulated if present
TITLES = {'fr30': 'FR30 chair / Clifford Q8 (reference)', 'cube': 'unit cube / FR30-type decoration / Clifford (pinned 6)',
          'randdec1': 'chair / random admissible decoration, seed 1', 'randdec2': 'chair / random admissible decoration, seed 2',
          'randdec3': 'chair / random admissible decoration, seed 3', 'stripped': 'FR30 graph / sign-stripped links (+ class rep.)',
          'randq8': 'FR30 graph / i.i.d. random Q8 links (seed 11)', 'trivial': 'FR30 graph / trivial links (no flux)',
          'randdec4': 'chair / random admissible decoration, seed 4 (suppl.)', 'randdec5': 'chair / random admissible decoration, seed 5 (suppl.)',
          'randdec6': 'chair / random admissible decoration, seed 6 (suppl.)'}
KNOWN = {'fr30': {3: 6.424, 4: 9.146, 5: 20.0}, 'cube': {3: 7.836, 4: 10.292}, 'trivial': {3: 2.259, 4: 2.885}}
KNOWN_E = {'fr30': {3: 9.37847, 4: 8.91963, 5: 8.79701}}
K = 4

def maxrss_gb(): return resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 1e6

class Log:
    def __init__(self, tag):
        self.fh = open(os.path.join(RES, f'phase5a_scaling_controls_{tag}.txt'), 'w')
    def __call__(self, msg=''):
        print(msg, flush=True); self.fh.write(msg + '\n'); self.fh.flush()

def jdump(obj, tag):
    with open(os.path.join(RES, f'phase5a_scaling_controls_{tag}.json'), 'w') as f: json.dump(obj, f, indent=1, default=conv)
def jload(tag):
    p = os.path.join(RES, f'phase5a_scaling_controls_{tag}.json')
    return json.load(open(p)) if os.path.exists(p) else None

# ---------------------------------------------------------------- decorations
def random_decoration(seed):
    """One parity-admissible chair decoration from np.random.default_rng(seed); redraw if it equals FR30."""
    rng = np.random.default_rng(seed); draws = 0
    while True:
        draws += 1
        d = {'0': EVEN[rng.integers(3)]}
        for v in U3: d[v] = (EVEN if sum(v) % 2 == 0 else ODD)[rng.integers(3)]
        if d != FR30: return d, draws

def geometry(system, level):
    """tiles, edges, deg, bulk coordination, decoration table."""
    if system == 'cube':
        dec = {v: FR30.get(v, (0, 2, 1)) for v in V8}
        tiles = cube_tiles(dec, level); owner, edges = panel_edges(tiles); deg = degrees(len(tiles), edges)
        assert deg.max() == 6; return tiles, edges, deg, 6, dec
    if system.startswith('randdec'):
        dec, _ = random_decoration(int(system[7:]))
    else: dec = FR30
    tiles, edges, deg = chair(dec, level); assert deg.max() == 24
    return tiles, edges, deg, 24, dec

def links_for(system, tiles, edges):
    if system == 'trivial': return [I2] * len(edges)
    if system == 'randq8':
        idx = np.random.default_rng(11).integers(0, 8, len(edges)); return [Q8[i] for i in idx]
    L = clifford_links(tiles, edges)
    if system == 'stripped': return [C if q8label(C)[0] == '+' else -C for C in L]
    return L

# ---------------------------------------------------------------- solvers
def finalize(H, w, V, k):
    o = np.argsort(w.real)[:k]; V = V[:, o]; V = V / np.linalg.norm(V, axis=0)
    HV = H @ V; lam = np.real(np.einsum('ij,ij->j', V.conj(), HV)); res = np.linalg.norm(HV - V * lam, axis=0)
    return lam, V, res
def eig_dense(H, k):
    A = H.toarray(order='F')
    w, V = sla.eigh(A, subset_by_index=(0, k - 1), driver='evr', overwrite_a=True, check_finite=False); del A
    return finalize(H, w, V, k)
def eig_lobpcg(H, k, extra=2, seed=0, tol=1e-7, maxiter=8000):
    rng = np.random.default_rng(seed); N = H.shape[0]
    X = rng.standard_normal((N, k + extra)) + 1j * rng.standard_normal((N, k + extra))
    dinv = 1.0 / H.diagonal().real
    M = spl.LinearOperator(H.shape, matvec=lambda v: dinv * v, matmat=lambda B: dinv[:, None] * B, dtype=complex)
    with warnings.catch_warnings(record=True) as wl:
        warnings.simplefilter('always'); w, V = spl.lobpcg(H, X, M=M, largest=False, tol=tol, maxiter=maxiter)
    lam, V, res = finalize(H, w, V, k)
    return lam, V, res, [str(x.message).split('\n')[0] for x in wl]

# ---------------------------------------------------------------- diagnostics
def interface_sets(level, edges):
    """I_d = tiles incident to a panel whose two tiles lie in different depth-d children (child = index // 8^(level-d))."""
    a, b = edge_arrays(edges); out = {}
    for d in range(1, level + 1):
        q = 8 ** (level - d); m = (a // q) != (b // q)
        out[d] = np.unique(np.concatenate([a[m], b[m]]))
    return out
def ground_stats(lam, V, deg, bulk, level, interf):
    p1 = tile_density(V[:, 0]); p2 = tile_density(V[:, 1]); p = 0.5 * (p1 + p2); n = len(p)
    ipr = float((p**2).sum()); ps = np.sort(p)[::-1]; cum = np.cumsum(ps)
    st = dict(n=n, ipr=ipr, ipr_n=ipr * n, P=1.0 / ipr, ipr_vec1=float((p1**2).sum()), ipr_vec2=float((p2**2).sum()),
              kramers_split=float(lam[1] - lam[0]), gap_to_next_pair=float(lam[2] - lam[0]),
              boundary_weight=float(p[deg < bulk].sum()), boundary_tile_fraction=float((deg < bulk).mean()), n_boundary=int((deg < bulk).sum()),
              p_max=float(ps[0]), s50=int(np.searchsorted(cum, 0.5) + 1), s90=int(np.searchsorted(cum, 0.9) + 1), S2={}, inv_S2={}, S3={},
              interface_weight={}, interface_fraction={}, interface_count={}, interface_enhancement={})
    for d in range(0, level + 1):
        W = p.reshape(8 ** d, 8 ** (level - d)).sum(axis=1)
        st['S2'][d] = float((W**2).sum()); st['inv_S2'][d] = 1.0 / st['S2'][d]; st['S3'][d] = float((W**3).sum())
        if d == 1: st['child_weights_depth1'] = W.tolist()
    for d in range(1, level + 1):
        I = interf[d]; st['interface_weight'][d] = float(p[I].sum()); st['interface_fraction'][d] = len(I) / n; st['interface_count'][d] = int(len(I))
        st['interface_enhancement'][d] = st['interface_weight'][d] / (len(I) / n)
    return st

def run_level(system, level, log, dense_upto=3):
    t0 = time.time(); tiles, edges, deg, bulk, dec = geometry(system, level); n = len(tiles); links = links_for(system, tiles, edges)
    labels = dict(collections.Counter(q8label(C) for C in links))
    H = build_H(n, edges, links, np.full(n, float(bulk))); assert abs(H - H.getH()).max() < 1e-12
    interf = interface_sets(level, edges); tb = time.time() - t0
    log(f"[{system}] level {level}: n={n} dim={H.shape[0]} |E|={len(edges)} nnz={H.nnz} bulk coordination {bulk}, boundary tiles {(deg < bulk).sum()}"
        f" ({(deg < bulk).mean():.3f}); interface tile counts {{d: |I_d|}} = { {d: len(interf[d]) for d in interf} }; link labels {labels}; build {tb:.1f}s")
    t0 = time.time()
    if H.shape[0] <= 8192 and level <= dense_upto:
        lam, V, res = eig_dense(H, K); how = 'dense eigh (evr, subset_by_index=(0,3))'; warns = []
    else:
        extra = 4 if level <= 4 else 2
        lam, V, res, warns = eig_lobpcg(H, K, extra=extra); how = f'lobpcg(block={K + extra}, seed=0, tol=1e-7, diag precond)'
    dt = time.time() - t0; st = ground_stats(lam, V, deg, bulk, level, interf)
    rec = dict(system=system, level=level, dim=int(H.shape[0]), n_edges=len(edges), nnz=int(H.nnz), bulk=bulk, link_labels=labels,
               eigenvalues=lam.tolist(), residuals=res.tolist(), solver=how, solver_warnings=warns, solve_seconds=dt, build_seconds=tb,
               maxrss_gb=maxrss_gb(), **st)
    log(f"   {how} ({dt:.0f}s, maxrss {maxrss_gb():.2f} GB){'  warnings: ' + '; '.join(warns) if warns else ''}")
    log(f"   lowest {K}: {np.array2string(lam, precision=7, max_line_width=200)}   residuals: {np.array2string(res, precision=1, max_line_width=200)}")
    log(f"   ground pair (split {st['kramers_split']:.1e}, gap to next pair {st['gap_to_next_pair']:.5f}): IPR={st['ipr']:.6g} [vec1 {st['ipr_vec1']:.6g}, vec2 {st['ipr_vec2']:.6g}]"
        f"  IPR*n={st['ipr_n']:.4f}  P={st['P']:.1f}  p_max={st['p_max']:.3g} s50={st['s50']} s90={st['s90']}  boundary weight={st['boundary_weight']:.4f} (tile fraction {st['boundary_tile_fraction']:.3f})")
    log("   S2(d)    d=1..L: " + "  ".join(f"{st['S2'][d]:.5f}" for d in range(1, level + 1)) +
        "   1/S2(d): " + "  ".join(f"{st['inv_S2'][d]:.3f}" for d in range(1, level + 1)) + "   (uniform: " + "  ".join(f"{8**d}" for d in range(1, level + 1)) + ")")
    log("   interface weight w(d) [tile fraction |I_d|/n, enhancement w/f]: " +
        "  ".join(f"d={d}: {st['interface_weight'][d]:.4f} [{st['interface_fraction'][d]:.4f}, {st['interface_enhancement'][d]:.3f}]" for d in range(1, level + 1)))
    log(f"   depth-1 child weights: {np.array2string(np.array(st['child_weights_depth1']), precision=4, max_line_width=200)}")
    if system in KNOWN and level in KNOWN[system]:
        log(f"   check vs known IPR*n {KNOWN[system][level]}: diff {st['ipr_n'] - KNOWN[system][level]:+.4f}" +
            (f";  vs known E0 {KNOWN_E[system][level]}: diff {lam[0] - KNOWN_E[system][level]:+.2e}" if system in KNOWN_E and level in KNOWN_E[system] else ''))
    return rec, dec

def scaling_rows(recs):
    recs = sorted(recs, key=lambda r: r['level']); out = []
    for r1, r2 in zip(recs, recs[1:]):
        alpha = float(-np.log(r2['ipr'] / r1['ipr']) / np.log(8))
        inv1 = {int(k): v for k, v in r1['inv_S2'].items()}; inv2 = {int(k): v for k, v in r2['inv_S2'].items()}
        row = dict(levels=[r1['level'], r2['level']], alpha=alpha, ipr_n_ratio=r2['ipr_n'] / r1['ipr_n'],
                   bottom_decrement=r1['eigenvalues'][0] - r2['eigenvalues'][0],
                   inv_S2_ratio={d: inv2[d] / inv1[d] for d in range(1, r1['level'] + 1)})
        out.append(row)
    return out

def part_system(system, maxlevel):
    log = Log(system); log(f"=== {system}: {TITLES[system]} ===   (pinned operator; python {sys.version.split()[0]}, numpy {np.__version__}, OMP_NUM_THREADS={os.environ.get('OMP_NUM_THREADS')})")
    out = dict(system=system, title=TITLES[system], records=[])
    if system.startswith('randdec'):
        seed = int(system[7:]); dec, draws = random_decoration(seed)
        out['decoration'] = {str(k): list(v) for k, v in dec.items()}; out['decoration_seed'] = seed; out['decoration_draws'] = draws
        log(f"   decoration seed {seed} (draw {draws}), permutation table pi_v (frame M_v = D_s(v) P(pi_v), P(pi)[i, pi_i] = 1):")
        for k in ['0'] + U3: log(f"      {str(k):<10} -> {dec[k]}   ({'FR30 same' if FR30[k] == dec[k] else 'FR30 ' + str(FR30[k])})")
        for lvl in (1, 2, 3):
            ov, exact, nc, nt = check_tiling(tiles_at_level(dec, lvl), lvl); assert ov == 0 and exact, 'decoration does not tile'
        log("   tiling check (levels 1-3): no overlaps, exact chair supertile")
    elif system == 'cube':
        dec = {v: FR30.get(v, (0, 2, 1)) for v in V8}; out['decoration'] = {str(k): list(v) for k, v in dec.items()}
        log("   decoration: " + ', '.join(f"{v}:{dec[v]}" for v in V8))
    else:
        out['decoration'] = {str(k): list(v) for k, v in FR30.items()}
    for level in range(3, maxlevel + 1):
        rec, _ = run_level(system, level, log); out['records'].append(rec)
    out['scaling'] = scaling_rows(out['records'])
    for s in out['scaling']:
        log(f"   scaling {s['levels'][0]}->{s['levels'][1]}: IPR*n ratio {s['ipr_n_ratio']:.3f}, alpha = -log(IPR_(k+1)/IPR_k)/log 8 = {s['alpha']:.3f};"
            f" 1/S2(d) growth ratios: " + ", ".join(f"d={d}: {v:.3f}" for d, v in s['inv_S2_ratio'].items()) + f"; bottom decrement {s['bottom_decrement']:+.5f}")
    jdump(out, system); log(f"   saved; maxrss {maxrss_gb():.2f} GB")

# ---------------------------------------------------------------- dense level-4 cross-check (separate pass; ~1.2 GB, slow under load)
def part_dense4(system):
    out = jload(system); assert out, f'run {system} first'
    rec = next(r for r in out['records'] if r['level'] == 4)
    fh = open(os.path.join(RES, f'phase5a_scaling_controls_{system}.txt'), 'a')
    def log(msg=''): print(msg, flush=True); fh.write(msg + '\n'); fh.flush()
    t0 = time.time(); tiles, edges, deg, bulk, dec = geometry(system, 4); n = len(tiles); links = links_for(system, tiles, edges)
    H = build_H(n, edges, links, np.full(n, float(bulk))); interf = interface_sets(4, edges)
    lam, V, res = eig_dense(H, K); st = ground_stats(lam, V, deg, bulk, 4, interf); dt = time.time() - t0
    chk = dict(eigenvalues=lam.tolist(), residuals=res.tolist(), ipr_n=st['ipr_n'], S2={d: st['S2'][d] for d in st['S2']},
               max_eig_diff_vs_lobpcg=float(np.abs(np.array(rec['eigenvalues']) - lam).max()), ipr_n_diff_vs_lobpcg=float(st['ipr_n'] - rec['ipr_n']),
               max_S2_diff_vs_lobpcg=float(max(abs(st['S2'][d] - rec['S2'][str(d)]) for d in st['S2'])), seconds=dt, maxrss_gb=maxrss_gb())
    rec['dense_check'] = chk
    log(f"[{system}] level 4 DENSE CROSS-CHECK (eigh evr subset (0,3), {dt:.0f}s, maxrss {maxrss_gb():.2f} GB): lowest 4 {np.array2string(lam, precision=7, max_line_width=200)}"
        f" residuals {np.array2string(res, precision=1, max_line_width=200)}; max|E_dense - E_lobpcg| = {chk['max_eig_diff_vs_lobpcg']:.2e};"
        f" IPR*n dense {st['ipr_n']:.5f} (diff vs lobpcg {chk['ipr_n_diff_vs_lobpcg']:+.1e}); max|S2 diff| {chk['max_S2_diff_vs_lobpcg']:.1e}")
    if system == 'fr30':
        pth = os.path.join(RES, 'level4_clifford_pinned_eigs.npy')
        if os.path.exists(pth):
            ref = np.load(pth)[:K]; chk['max_diff_vs_phase5_dense_reference'] = float(np.abs(ref - lam).max())
            log(f"   vs phase-5 saved dense level-4 pinned eigenvalues: max|diff| = {chk['max_diff_vs_phase5_dense_reference']:.2e}")
    jdump(out, system)

# ---------------------------------------------------------------- table
def part_table():
    log = Log('table'); data = {s: jload(s) for s in SYSTEMS + EXTRA}; data = {s: d for s, d in data.items() if d}
    merged = dict(conventions=__doc__, systems=data)
    log("TASK C1: LEVEL-5 PARTICIPATION SCALING OF THE PINNED GROUND STATE, FR30 AND CONTROLS (numerical evidence; all numbers from this run)")
    log("alpha_(k->k+1) = -log(IPR_(k+1)/IPR_k)/log 8 (1 extended, 0 localized); IPR*n = 1 for a uniform state; 1/S2(d) = effective number of occupied depth-d children (8^d uniform)\n")
    def rec(s, l): return next((r for r in data[s]['records'] if r['level'] == l), None)
    hdr = (f"{'system':<52} {'E0 L3':>9} {'E0 L4':>9} {'E0 L5':>9} {'E0 L6':>9} | {'IPR*n L3':>8} {'IPR*n L4':>8} {'IPR*n L5':>8} {'IPR*n L6':>8} | "
           f"{'a(3->4)':>7} {'a(4->5)':>7} {'a(5->6)':>7} | {'ratio45':>7} {'bw L5':>6} {'max res':>8}")
    log(hdr); log('-' * len(hdr)); rows = []
    for s, d in data.items():
        R = {r['level']: r for r in d['records']}; sc = {tuple(x['levels']): x for x in d['scaling']}
        e = [R[l]['eigenvalues'][0] if l in R else None for l in (3, 4, 5, 6)]; ip = [R[l]['ipr_n'] if l in R else None for l in (3, 4, 5, 6)]
        al = [sc[(3, 4)]['alpha'] if (3, 4) in sc else None, sc[(4, 5)]['alpha'] if (4, 5) in sc else None, sc[(5, 6)]['alpha'] if (5, 6) in sc else None]
        r45 = sc[(4, 5)]['ipr_n_ratio'] if (4, 5) in sc else None; bw5 = R[5]['boundary_weight'] if 5 in R else None
        mr = max(max(r['residuals']) for r in R.values()); dc = R[4].get('dense_check') if 4 in R else None
        f = lambda x, w=9, p=5: f"{x:{w}.{p}f}" if x is not None else f"{'-':>{w}}"
        log(f"{TITLES[s]:<52} {f(e[0])} {f(e[1])} {f(e[2])} {f(e[3])} | {f(ip[0],8,3)} {f(ip[1],8,3)} {f(ip[2],8,3)} {f(ip[3],8,3)} | {f(al[0],7,3)} {f(al[1],7,3)} {f(al[2],7,3)} | {f(r45,7,3)} {f(bw5,6,4)} {mr:8.1e}"
            + (f"  dense L4 check: max|dE| {dc['max_eig_diff_vs_lobpcg']:.1e}, dIPR*n {dc['ipr_n_diff_vs_lobpcg']:+.1e}" if dc else "  (no dense L4 check)"))
        rows.append(dict(system=s, title=TITLES[s], E0={l: e[i] for i, l in enumerate((3, 4, 5, 6))}, ipr_n={l: ip[i] for i, l in enumerate((3, 4, 5, 6))},
                         alpha={'3->4': al[0], '4->5': al[1], '5->6': al[2]}, ipr_n_ratio_45=r45, boundary_weight_L5=bw5, max_residual=mr,
                         dense_L4_check=dict(max_eig_diff=dc['max_eig_diff_vs_lobpcg'], ipr_n_diff=dc['ipr_n_diff_vs_lobpcg']) if dc else None))
    merged['table'] = rows
    log("\nLOWEST 4 EIGENVALUES AND RESIDUALS")
    for s, d in data.items():
        for r in d['records']:
            log(f"  {TITLES[s]:<52} L{r['level']}: {np.array2string(np.array(r['eigenvalues']), precision=6, max_line_width=200)}  res max {max(r['residuals']):.1e}  [{r['solver']}, {r['solve_seconds']:.0f}s]")
    log("\nBOX COUNTING: effective number of occupied depth-d children 1/S2(d) (uniform: 8^d), per level")
    for s, d in data.items():
        for r in d['records']:
            L = r['level']; inv = {int(k): v for k, v in r['inv_S2'].items()}
            log(f"  {TITLES[s]:<52} L{L}: " + "  ".join(f"d={dd}: {inv[dd]:8.3f} ({inv[dd]/8**dd:.3f})" for dd in range(1, L + 1)))
    log("\n1/S2(d) GROWTH RATIOS AT FIXED DEPTH d BETWEEN CONSECUTIVE LEVELS (1 = same number of occupied depth-d children; the depth-d children are 8x larger at the next level)")
    for s, d in data.items():
        for sc in d['scaling']:
            log(f"  {TITLES[s]:<52} {sc['levels'][0]}->{sc['levels'][1]}: " + "  ".join(f"d={dd}: {v:.3f}" for dd, v in sc['inv_S2_ratio'].items()))
    log("\nWITHIN-LEVEL BRANCHING S2(d)/S2(d+1) (occupied sub-children per occupied child; 8 uniform)")
    for s, d in data.items():
        for r in d['records']:
            L = r['level']; S = {int(k): v for k, v in r['S2'].items()}
            log(f"  {TITLES[s]:<52} L{L}: " + "  ".join(f"d={dd}->{dd+1}: {S[dd]/S[dd+1]:.3f}" for dd in range(0, L)))
    log("\nINTERFACE WEIGHTS w(d) [tile fraction |I_d|/n] AND BOUNDARY WEIGHT")
    for s, d in data.items():
        for r in d['records']:
            L = r['level']; w = {int(k): v for k, v in r['interface_weight'].items()}; fr = {int(k): v for k, v in r['interface_fraction'].items()}
            log(f"  {TITLES[s]:<52} L{L}: " + "  ".join(f"d={dd}: {w[dd]:.4f} [{fr[dd]:.4f}]" for dd in range(1, L + 1)) + f"   boundary {r['boundary_weight']:.4f} [{r['boundary_tile_fraction']:.3f}]")
    # ---- verdicts
    log("\nCOMPARISON WITH FR30 (two-point exponent alpha(4->5) and IPR*n ratio 4->5; criterion stated explicitly)")
    ref = next((x for x in rows if x['system'] == 'fr30'), None); verdict = {}
    if ref and ref['alpha']['4->5'] is not None:
        a0 = ref['alpha']['4->5']; a034 = ref['alpha']['3->4']
        log(f"  FR30: alpha(3->4) = {a034:.3f}, alpha(4->5) = {a0:.3f}, IPR*n ratio 4->5 = {ref['ipr_n_ratio_45']:.3f}")
        log("  'shares the FR30 growth' := |alpha_sys(4->5) - alpha_FR30(4->5)| <= 0.10 ; 'does not share' := difference >= 0.25 ; otherwise 'ambiguous'")
        for x in rows:
            if x['system'] == 'fr30' or x['alpha']['4->5'] is None: continue
            da = x['alpha']['4->5'] - a0; v = 'shares' if abs(da) <= 0.10 else ('does not share' if abs(da) >= 0.25 else 'ambiguous')
            verdict[x['system']] = dict(alpha45=x['alpha']['4->5'], diff=da, verdict=v)
            log(f"  {TITLES[x['system']]:<52} alpha(4->5) = {x['alpha']['4->5']:.3f} (diff {da:+.3f}), IPR*n ratio {x['ipr_n_ratio_45']:.3f}  -> {v}")
        ex = [verdict[s]['verdict'] for s in EXTRA if s in verdict]
        if ex: log(f"  supplementary random decorations (seeds 4-6, not part of the task list): {ex}")
        l6 = [(x['title'], x['alpha']['5->6']) for x in rows if x['alpha'].get('5->6') is not None]
        if l6: log("  level-6 two-point exponents where computed: " + "; ".join(f"{t}: alpha(5->6) = {a:.3f}" for t, a in l6) + "   [FR30 known level-6 value, NOT computed here: IPR*n = 0.00016*262144 = 41.9 -> alpha(5->6) ~ 0.64]")
        rd = [verdict[s]['verdict'] for s in ('randdec1', 'randdec2', 'randdec3') if s in verdict]; cb = verdict.get('cube', {}).get('verdict')
        rq = verdict.get('randq8', {}).get('verdict'); st = verdict.get('stripped', {}).get('verdict'); tr = verdict.get('trivial', {}).get('verdict')
        log(f"\n  (a) random decorations of the chair: {rd}; (b) cube geometry, same decoration rule: {cb}; (c) random links: {rq}; sign-stripped: {st}; (d) no flux: {tr}")
        if rd and all(v == 'shares' for v in rd) and cb == 'does not share':
            concl = 'the IPR*n growth is a property of the chair geometry with aperiodic Q8 decoration (shared by the random chair decorations, not by the cube control)'
        elif cb == 'shares':
            concl = 'the IPR*n growth is a property of the decoration hierarchy (shared by the cube control)'
        elif rd and all(v == 'does not share' for v in rd) and cb == 'does not share' and rq == 'does not share' and tr == 'does not share':
            concl = 'the IPR*n growth is specific to FR30 (not shared by any control)'
        else:
            concl = 'the data are not clean enough to decide between the alternatives (mixed or ambiguous verdicts)'
        log(f"  VERDICT (numerical evidence, levels 3-5 only): {concl}")
        merged['verdict'] = dict(criterion='|alpha_sys(4->5) - alpha_FR30(4->5)| <= 0.10 shares; >= 0.25 does not share; else ambiguous', per_system=verdict, conclusion=concl)
    with open(os.path.join(RES, 'phase5a_scaling_controls.json'), 'w') as fh: json.dump(merged, fh, indent=1, default=conv)
    os.replace(os.path.join(RES, 'phase5a_scaling_controls_table.txt'), os.path.join(RES, 'phase5a_scaling_controls.txt'))

if __name__ == '__main__':
    part = sys.argv[1] if len(sys.argv) > 1 else 'all'
    maxlevel = int(sys.argv[2]) if len(sys.argv) > 2 and sys.argv[2].isdigit() else 5
    if part == 'table': part_table()
    elif part == 'all':
        env = dict(os.environ, OMP_NUM_THREADS='1', OPENBLAS_NUM_THREADS='1', MKL_NUM_THREADS='1')
        for s in SYSTEMS:
            t0 = time.time(); print(f"##### running {s}", flush=True)
            rc = subprocess.run([sys.executable, '-u', '-I', os.path.abspath(__file__), s, str(maxlevel)], env=env).returncode
            print(f"##### {s} finished rc={rc} in {time.time()-t0:.0f}s", flush=True)
        part_table()
    elif part == 'dense4all':
        env = dict(os.environ, OMP_NUM_THREADS='1', OPENBLAS_NUM_THREADS='1', MKL_NUM_THREADS='1')
        for s in (sys.argv[2:] or SYSTEMS):
            t0 = time.time(); print(f"##### dense level-4 check {s}", flush=True)
            rc = subprocess.run([sys.executable, '-u', '-I', os.path.abspath(__file__), 'dense4', s], env=env).returncode
            print(f"##### dense4 {s} finished rc={rc} in {time.time()-t0:.0f}s", flush=True)
        part_table()
    elif part == 'dense4': part_dense4(sys.argv[2])
    elif part in SYSTEMS: part_system(part, maxlevel)
    else: raise SystemExit(__doc__)
