#!/usr/bin/env python3
"""
Phase 5a / task B2b: matched controls and stability tests for the spectral bottom of the PINNED Clifford hopping
operator on the FR30 Chair44 tiling (research targets H2 / H3).

Operator conventions (identical to audit/phase5_bulk_bottom_lobpcg.py):
  Hilbert space l^2(tiles) x C^2.  (A psi)_a = sum over shared unit panels f=(a,b) of C_ab psi_b with
  C_ab = (sigma.M_a^T n_f)(sigma.M_b^T n_f) in Q8 and C_ba = C_ab^dagger; panels between the same pair of tiles are
  summed with multiplicity.  H_free = D - A (D_aa = number of shared panels of tile a, times I_2);
  H_pin = 24 I - A (bulk coordination 24 on every tile); Robin: d_a = deg_a + t (24 - deg_a).
  Unit-cube control: bulk coordination 6, pinned diagonal 6.
Tile IPR normalization (stated as required): for a normalized eigenvector psi, p_a = |psi_{a,1}|^2 + |psi_{a,2}|^2
  (sum_a p_a = 1), IPR = sum_a p_a^2, participation number P = 1/IPR; a state uniform over all n tiles has IPR = 1/n,
  a state uniform over s tiles has IPR = 1/s.  The ground state is a Kramers pair (T = 1 x i sigma_y K): psi_a and
  (T psi)_a are orthogonal spinors at every tile, so p_a is the same for every unit vector of the 2-dim eigenspace.
  We report the IPR of the pair-averaged density and the IPR of each of the two returned vectors as a check.
Solvers: level <= 3 dense eigh (full spectrum); level >= 4 matrix-free LOBPCG with diagonal preconditioner and a
  fixed seed (k requested + 2 guard vectors), eigenvalues recomputed as Rayleigh quotients of the normalized Ritz
  vectors; residual norms ||H psi - lambda psi||_2 are reported for every eigenpair.  The level-4 LOBPCG values are
  cross-checked against a dense eigvalsh in part 'gauge'.
Run from the repository root (each part is a separate process; all parts < 40 min and < 3.5 GB):
  python3 -u -I audit/phase5a_controls.py chair {clifford|trivial|stripped|randq8} [maxlevel]
  python3 -u -I audit/phase5a_controls.py randdec i j k ...        (random admissible decorations, indices 0..5)
  python3 -u -I audit/phase5a_controls.py perturb | gauge | robin | cube [maxlevel] | table
Outputs: audit/results/phase5a_controls_<part>.txt/.json per part; 'table' merges everything into
  audit/results/phase5a_controls.json and audit/results/phase5a_controls.txt.
"""
import os, sys, time, json, warnings, collections, itertools
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
RES = os.path.join(HERE, 'results')
import numpy as np, scipy.sparse as sps, scipy.sparse.linalg as spl, scipy.linalg as sla
from independent_clifford_q8_audit import (U3, FR30, perm_mat, tiles_at_level, panel_edges, clifford_link, q8label,
                                           check_tiling, SIG)

PERMS = list(itertools.permutations(range(3)))
def sgn(p): return int(round(np.linalg.det(perm_mat(p))))
EVEN = [p for p in PERMS if sgn(p) == 1]; ODD = [p for p in PERMS if sgn(p) == -1]
V8 = list(itertools.product((0, 1), repeat=3))
Q8 = [np.eye(2, dtype=complex), -np.eye(2, dtype=complex)] + [s * 1j * SIG[k] for k in range(3) for s in (1, -1)]
I2 = np.eye(2, dtype=complex)
EPS = [0.01, 0.05, 0.1, 0.2]
ROBIN_T = [0.0, 0.125, 0.25, 0.375, 0.5, 0.625, 0.75, 0.875, 1.0]
DEC_SEED = 20261021

class Log:
    def __init__(self, tag):
        self.fh = open(os.path.join(RES, f'phase5a_controls_{tag}.txt'), 'w')
    def __call__(self, msg=''):
        print(msg, flush=True); self.fh.write(msg + '\n'); self.fh.flush()

def conv(o):
    if isinstance(o, np.integer): return int(o)
    if isinstance(o, np.floating): return float(o)
    if isinstance(o, np.ndarray): return o.tolist()
    if isinstance(o, (frozenset, set, tuple)): return list(o)
    raise TypeError(str(type(o)))
def jdump(obj, tag):
    with open(os.path.join(RES, f'phase5a_controls_{tag}.json'), 'w') as f: json.dump(obj, f, indent=1, default=conv)
def jload(tag):
    p = os.path.join(RES, f'phase5a_controls_{tag}.json')
    return json.load(open(p)) if os.path.exists(p) else None

# ---------------------------------------------------------------- geometry
def degrees(n, edges):
    deg = np.zeros(n, int)
    for a, b, _, _, _ in edges: deg[a] += 1; deg[b] += 1
    return deg
def chair(frames, level):
    tiles = tiles_at_level(frames, level); owner, edges = panel_edges(tiles)
    return tiles, edges, degrees(len(tiles), edges)
def cube_tiles(dec, level):
    ops = [(np.diag([1-2*v[0], 1-2*v[1], 1-2*v[2]]) @ perm_mat(dec[v]), 2*np.array(v)) for v in V8]
    poses = [(np.eye(3, dtype=int), np.zeros(3, dtype=int))]
    for _ in range(level): poses = [(G @ g, 2*T + G @ t) for G, T in poses for g, t in ops]
    tiles = [(G, T, frozenset([tuple((G @ np.array([1, 1, 1]) + 2*T - 1) // 2)])) for G, T in poses]
    L = 2**level; cubes = {next(iter(cs)) for _, _, cs in tiles}
    assert len(cubes) == len(tiles) == L**3 and all(0 <= x < L for c in cubes for x in c), 'cube control does not tile the box'
    for G, _, _ in tiles: assert (G.T @ G == np.eye(3, dtype=int)).all() and round(np.linalg.det(G)) == 1
    return tiles
def clifford_links(tiles, edges):
    cache = {}; out = []
    for a, b, nf, _, _ in edges:
        key = (a, b, int(np.argmax(nf))); C = cache.get(key)
        if C is None: C = clifford_link(tiles[a][0], tiles[b][0], nf); cache[key] = C
        out.append(C)
    return out
def edge_arrays(edges):
    m = len(edges)
    return np.fromiter((e[0] for e in edges), int, m), np.fromiter((e[1] for e in edges), int, m)

def build_H(n, edges, links, diag):
    """Sparse Hermitian H = diag(d_a I_2) - A with A_ab = sum over panels (a,b) of C_ab (C_ba = C_ab^dagger)."""
    a, b = edge_arrays(edges); m = len(edges)
    L = np.asarray(links, dtype=complex).reshape(m, 2, 2)
    rows, cols, vals = [], [], []
    for r in range(2):
        for c in range(2):
            rows += [2*a + r, 2*b + c]; cols += [2*b + c, 2*a + r]; vals += [-L[:, r, c], -np.conj(L[:, r, c])]
    idx = np.arange(2*n); rows.append(idx); cols.append(idx)
    vals.append(np.repeat(np.asarray(diag, float), 2).astype(complex))
    return sps.coo_matrix((np.concatenate(vals), (np.concatenate(rows), np.concatenate(cols))), shape=(2*n, 2*n)).tocsr()

# ---------------------------------------------------------------- solvers
def finalize(H, w, V, k):
    o = np.argsort(w.real)[:k]; V = V[:, o]; V = V / np.linalg.norm(V, axis=0)
    HV = H @ V; lam = np.real(np.einsum('ij,ij->j', V.conj(), HV)); res = np.linalg.norm(HV - V * lam, axis=0)
    return lam, V, res
def eig_dense(H, k):
    w, V = sla.eigh(H.toarray()); lam, V, res = finalize(H, w, V, k); return lam, V, res, w
def eig_lobpcg(H, k, extra=2, seed=0, tol=1e-7, maxiter=6000):
    rng = np.random.default_rng(seed); N = H.shape[0]
    X = rng.standard_normal((N, k + extra)) + 1j * rng.standard_normal((N, k + extra))
    dinv = 1.0 / H.diagonal().real
    M = spl.LinearOperator(H.shape, matvec=lambda v: dinv * v, matmat=lambda B: dinv[:, None] * B, dtype=complex)
    with warnings.catch_warnings():
        warnings.simplefilter('ignore'); w, V = spl.lobpcg(H, X, M=M, largest=False, tol=tol, maxiter=maxiter)
    lam, V, res = finalize(H, w, V, k); return lam, V, res, None

def tile_density(v):
    p = np.abs(v[0::2])**2 + np.abs(v[1::2])**2; return p / p.sum()
def ground_stats(lam, V, deg, bulk):
    p1 = tile_density(V[:, 0]); p2 = tile_density(V[:, 1]); p = 0.5 * (p1 + p2)
    n = len(p); ipr = float((p**2).sum()); ps = np.sort(p)[::-1]; cum = np.cumsum(ps)
    return dict(n=n, ipr=ipr, ipr_n=ipr * n, P=1.0 / ipr, ipr_vec1=float((p1**2).sum()), ipr_vec2=float((p2**2).sum()),
                kramers_split=float(lam[1] - lam[0]), boundary_weight=float(p[deg < bulk].sum()),
                boundary_tile_fraction=float((deg < bulk).mean()), n_boundary=int((deg < bulk).sum()), p_max=float(ps[0]),
                s50=int(np.searchsorted(cum, 0.5) + 1), s90=int(np.searchsorted(cum, 0.9) + 1))

def run(label, n, edges, deg, links, diag, bulk, level, k, log, dense_upto=3, k_solve=None, seed=0):
    t0 = time.time(); H = build_H(n, edges, links, diag)
    assert abs(H - H.getH()).max() < 1e-12, 'operator not Hermitian'
    if level <= dense_upto:
        lam, V, res, full = eig_dense(H, k); how = 'dense eigh'
    else:
        ks = k_solve or k + 2
        lam, V, res, full = eig_lobpcg(H, k, extra=ks - k, seed=seed); how = f'lobpcg(block={ks},seed={seed},tol=1e-7)'
    st = ground_stats(lam, V, deg, bulk); dt = time.time() - t0
    rec = dict(label=label, level=level, dim=int(H.shape[0]), n_edges=len(edges), nnz=int(H.nnz), eigenvalues=lam.tolist(),
               residuals=res.tolist(), solver=how, seconds=dt, **st)
    if full is not None:
        rec['full_spectrum_mean'] = float(full.mean()); rec['full_spectrum_max'] = float(full.max()); rec['full_spectrum'] = full
    log(f"[{label}] level {level} n={n} dim={H.shape[0]} |E|={len(edges)} {how} ({dt:.0f}s)")
    log(f"   lowest {k}: {np.array2string(lam, precision=6, max_line_width=220)}")
    log(f"   residuals ||H psi - lambda psi||: {np.array2string(res, precision=1, max_line_width=220)}")
    log(f"   ground state (Kramers pair, split {st['kramers_split']:.1e}): tile IPR={st['ipr']:.6g} [vec1 {st['ipr_vec1']:.6g}, vec2 {st['ipr_vec2']:.6g}]"
        f"  IPR*n={st['ipr_n']:.4f}  P=1/IPR={st['P']:.1f}  p_max={st['p_max']:.3g} s50={st['s50']} s90={st['s90']}"
        f"  boundary weight={st['boundary_weight']:.4f} (boundary tile fraction {st['boundary_tile_fraction']:.3f})")
    return rec, H, V

def scaling(out, log):
    recs = sorted(out['records'], key=lambda r: r['level']); sc = []
    for r1, r2 in zip(recs, recs[1:]):
        gamma = float(np.log(r1['ipr'] / r2['ipr']) / np.log(r2['n'] / r1['n']))
        sc.append(dict(levels=[r1['level'], r2['level']], gamma=gamma, ipr_n=[r1['ipr_n'], r2['ipr_n']], ratio_ipr_n=r2['ipr_n'] / r1['ipr_n'],
                       bottom=[r1['eigenvalues'][0], r2['eigenvalues'][0]], bottom_decrement=r1['eigenvalues'][0] - r2['eigenvalues'][0]))
        log(f"   scaling {r1['level']}->{r2['level']}: bottom {r1['eigenvalues'][0]:.5f} -> {r2['eigenvalues'][0]:.5f} (decrement {r1['eigenvalues'][0]-r2['eigenvalues'][0]:+.5f});"
            f" IPR*n {r1['ipr_n']:.3f} -> {r2['ipr_n']:.3f} (ratio {r2['ipr_n']/r1['ipr_n']:.3f}); IPR ~ n^(-gamma), gamma={gamma:.3f} (extended 1, localized 0)")
    out['scaling'] = sc
def strip_full(out):
    for r in out['records']: r.pop('full_spectrum', None)

# ---------------------------------------------------------------- part: chair models on the FR30 graph
CONV = {'clifford': 'FR30 Clifford Q8 links C_ab = (sigma.M_a^T n)(sigma.M_b^T n)',
        'trivial': 'all links I_2 on the FR30 graph (no flux)',
        'stripped': "sign-stripped / adjoint-only: each FR30 link replaced by its V4-class representative with positive sign (+1 or +i sigma_k) in the edge-list orientation a->b (= +axis direction of the panel normal); C_ba = C_ab^dagger",
        'randq8': 'i.i.d. uniform Q8 links on the FR30 graph, np.random.default_rng(11).integers(0,8,|E|) in edge-list order (same construction as phase5_dynamics_boundary.py)'}
def links_for(model, tiles, edges, log):
    if model == 'clifford': return clifford_links(tiles, edges)
    if model == 'trivial': return [I2] * len(edges)
    if model == 'stripped':
        L = clifford_links(tiles, edges); out = [C if q8label(C)[0] == '+' else -C for C in L]
        log(f"   link labels before: {dict(collections.Counter(q8label(C) for C in L))}  after stripping: {dict(collections.Counter(q8label(C) for C in out))}")
        return out
    if model == 'randq8':
        idx = np.random.default_rng(11).integers(0, 8, len(edges)); out = [Q8[i] for i in idx]
        log(f"   random Q8 label counts: {dict(collections.Counter(q8label(C) for C in out))}"); return out
    raise ValueError(model)
def part_chair(model, maxlevel):
    log = Log(f'chair_{model}'); log(f"=== chair / {model} (pinned, diagonal 24) ===\n   convention: {CONV[model]}")
    out = dict(model=model, convention=CONV[model], records=[])
    for level in range(3, maxlevel + 1):
        tiles, edges, deg = chair(FR30, level); n = len(tiles); links = links_for(model, tiles, edges, log)
        rec, H, V = run(f'chair/{model}/pinned', n, edges, deg, links, np.full(n, 24.0), 24, level, 8 if level <= 4 else 6, log)
        if level == 4 and model == 'clifford':
            p = os.path.join(RES, 'level4_clifford_pinned_eigs.npy')
            if os.path.exists(p):
                ref = np.load(p)[:8]; rec['phase5_dense_reference_lowest8'] = ref.tolist()
                log(f"   check vs phase-5 dense level-4 pinned eigenvalues: max|diff| = {np.abs(ref - np.array(rec['eigenvalues'])).max():.2e}")
        out['records'].append(rec)
    scaling(out, log); strip_full(out); jdump(out, f'chair_{model}')

# ---------------------------------------------------------------- part: random parity-admissible decorations
def random_decorations(seed=DEC_SEED, count=6):
    rng = np.random.default_rng(seed); decs = []
    while len(decs) < count:
        d = {'0': EVEN[rng.integers(3)]}
        for v in U3: d[v] = (EVEN if sum(v) % 2 == 0 else ODD)[rng.integers(3)]
        if d != FR30: decs.append(d)
    return decs
def part_randdec(indices):
    decs = random_decorations()
    for i in indices:
        d = decs[i]; log = Log(f'randdec{i}')
        log(f"=== chair / random parity-admissible decoration #{i} (rng seed {DEC_SEED}, draw {i}; frames M_v = D_s(v) P(pi_v), pi_v even for even-weight v, odd for odd-weight v, centre even) ===")
        log("   decoration: " + ', '.join(f"{k}:{d[k]}" for k in ['0'] + U3))
        for lvl in (1, 2):
            ov, exact, nc, nt = check_tiling(tiles_at_level(d, lvl), lvl); assert ov == 0 and exact, 'decoration does not tile'
        log("   tiling check (levels 1, 2): no overlaps, exact chair supertile; frames in SO(3,Z)")
        out = dict(index=i, seed=DEC_SEED, decoration={str(k): list(v) for k, v in d.items()}, records=[])
        for level in range(3, 6):
            tiles, edges, deg = chair(d, level); n = len(tiles); links = clifford_links(tiles, edges)
            if level == 3: log(f"   link labels: {dict(collections.Counter(q8label(C) for C in links))}")
            rec, H, V = run(f'chair/randdec{i}/pinned', n, edges, deg, links, np.full(n, 24.0), 24, level, 8 if level <= 4 else 6, log)
            out['records'].append(rec)
        scaling(out, log); strip_full(out); jdump(out, f'randdec{i}')

# ---------------------------------------------------------------- part: coupling perturbations
def part_perturb():
    log = Log('perturb')
    conv_txt = ('every FR30 link C_e replaced by C_e exp(i eps X_e), X_e = nhat_e . sigma with nhat_e uniform on S^2 (traceless Hermitian, operator norm 1); '
                'X_e drawn in edge-list order from np.random.default_rng(seed), seeds 101, 102, 103 (same seeds at both levels); pinned diagonal 24')
    log("=== coupling perturbations of the pinned FR30 operator ===\n   " + conv_txt)
    out = dict(convention=conv_txt, eps=EPS, seeds=[101, 102, 103], levels={})
    for level in (3, 4):
        tiles, edges, deg = chair(FR30, level); n = len(tiles); links = clifford_links(tiles, edges); diag = np.full(n, 24.0)
        L = np.asarray(links).reshape(len(edges), 2, 2); H0 = build_H(n, edges, links, diag)
        lam0, V0, res0, full0 = eig_dense(H0, 4) if level == 3 else eig_lobpcg(H0, 4, extra=2)
        if level == 3: _, Vfull = sla.eigh(H0.toarray()); wfull = full0
        log(f"\nlevel {level}: unperturbed pinned bottom {lam0[0]:.9f} (res {res0[0]:.1e}); Kramers partner {lam0[1]:.9f}; next pair {lam0[2]:.6f}")
        log(f"   <psi|A|psi> = 24 - lambda_0 = {24 - lam0[0]:.5f}; 'diagonal' eps^2 coefficient (from X_e^2 = 1): (24 - lambda_0)/2 = {(24 - lam0[0])/2:.5f}")
        lv = dict(lambda0=float(lam0[0]), res0=float(res0[0]), seeds={})
        for seed in (101, 102, 103):
            rng = np.random.default_rng(seed); nh = rng.standard_normal((len(edges), 3)); nh /= np.linalg.norm(nh, axis=1)[:, None]
            X = np.einsum('ej,jab->eab', nh, np.array(SIG))
            # first-order degenerate perturbation theory on the Kramers pair: dH1 = -(dA)^(1) with link increments i C X
            H1 = build_H(n, edges, 1j * np.einsum('eab,ebc->eac', L, X), np.zeros(n))
            P = V0[:, :2]; W1 = P.conj().T @ (H1 @ P); w1 = np.linalg.eigvalsh(0.5 * (W1 + W1.conj().T))
            sd = dict(first_order_coeff=w1.tolist(), rows=[])
            log(f"  seed {seed}: first-order (Kramers 2x2) coefficients a_PT = {w1[0]:+.6f}, {w1[1]:+.6f}  (shift ~ a_PT*eps; identical pair => T-symmetric)")
            if level == 3:
                # exact second-order degenerate PT at level 3 from the full dense spectrum
                Hm = Vfull.conj().T @ (H1 @ P)             # <m|H1|i>
                keep = np.abs(wfull - lam0[0]) > 1e-8
                W2 = (Hm[keep].conj().T * (1.0 / (lam0[0] - wfull[keep]))) @ Hm[keep] + 0.5 * (P.conj().T @ ((24.0 * P) - (H0 @ P)))
                w2 = np.linalg.eigvalsh(0.5 * (W2 + W2.conj().T)); sd['second_order_coeff_PT'] = w2.tolist()
                log(f"           exact second-order PT coefficient b_PT = {w2[0]:+.5f}, {w2[1]:+.5f}  (= (24-lambda0)/2 - sum_m |<m|H1|0>|^2/(E_m-E_0))")
            shifts = []
            for eps in EPS:
                Ue = np.cos(eps) * I2[None] + 1j * np.sin(eps) * X
                Le = np.einsum('eab,ebc->eac', L, Ue); He = build_H(n, edges, Le, diag)
                lam, V, res, _ = eig_dense(He, 4) if level == 3 else eig_lobpcg(He, 4, extra=2)
                dl = float(lam[0] - lam0[0]); shifts.append(dl)
                sd['rows'].append(dict(eps=eps, lambda0=float(lam[0]), lambda1=float(lam[1]), residual=float(res[0]), shift=dl, shift_over_eps=dl / eps, shift_over_eps2=dl / eps**2))
                log(f"    eps={eps:<5}: lambda_0={lam[0]:.9f} (res {res[0]:.1e})  shift={dl:+.3e}  shift/eps={dl/eps:+.4e}  shift/eps^2={dl/eps**2:+.4f}")
            E = np.array(EPS); S = np.array(shifts)
            A2 = np.vstack([E, E**2]).T; c2, *_ = np.linalg.lstsq(A2, S, rcond=None); r2 = S - A2 @ c2
            A3 = np.vstack([E, E**2, E**3]).T; c3, *_ = np.linalg.lstsq(A3, S, rcond=None); r3 = S - A3 @ c3
            sd['fit_a_eps_b_eps2'] = dict(a=float(c2[0]), b=float(c2[1]), max_resid=float(np.abs(r2).max()))
            sd['fit_a_b_c'] = dict(a=float(c3[0]), b=float(c3[1]), c=float(c3[2]), max_resid=float(np.abs(r3).max()))
            log(f"    fit shift = a eps + b eps^2       : a={c2[0]:+.5f} b={c2[1]:+.4f} (max fit resid {np.abs(r2).max():.1e})")
            log(f"    fit shift = a eps + b eps^2 + c eps^3: a={c3[0]:+.5f} b={c3[1]:+.4f} c={c3[2]:+.3f} (max fit resid {np.abs(r3).max():.1e});  a_PT={w1[0]:+.5f}")
            lv['seeds'][str(seed)] = sd
        out['levels'][str(level)] = lv
    jdump(out, 'perturb')

# ---------------------------------------------------------------- part: gauge equivalence at level 4 (dense)
def part_gauge():
    log = Log('gauge'); log("=== gauge-equivalent representations of the level-4 pinned FR30 operator (dense eigvalsh, dim 8192) ===")
    tiles, edges, deg = chair(FR30, 4); n = len(tiles); links = clifford_links(tiles, edges); diag = np.full(n, 24.0)
    H = build_H(n, edges, links, diag)
    rng = np.random.default_rng(5); q = rng.standard_normal((n, 4)); q /= np.linalg.norm(q, axis=1)[:, None]
    G = q[:, 0, None, None] * I2 + 1j * (q[:, 1, None, None] * SIG[0] + q[:, 2, None, None] * SIG[1] + q[:, 3, None, None] * SIG[2])
    assert np.allclose(np.einsum('aij,akj->aik', G, G.conj()), I2) and np.allclose(np.linalg.det(G), 1)
    a, b = edge_arrays(edges); L = np.asarray(links).reshape(-1, 2, 2)
    L2 = np.einsum('eij,ejk,elk->eil', G[a], L, G[b].conj())          # C'_ab = G_a C_ab G_b^dagger
    H2 = build_H(n, edges, L2, diag)
    U = sps.bsr_matrix((G, np.arange(n), np.arange(n + 1)), shape=(2*n, 2*n)).tocsr()
    dev = abs(H2 - U @ H @ U.getH()).max()
    log(f"   random local gauge G_a in SU(2) (Haar via normalized quaternions, rng seed 5), n={n} tiles")
    log(f"   max|H' - U H U^dagger| = {dev:.2e}  (H' built from transformed links, U = direct sum of G_a)")
    Dm = (H2 - H).tocsr(); offd = H - sps.diags(H.diagonal())
    changed = int((np.abs(Dm.data) > 1e-12).sum()); log(f"   off-diagonal nonzeros: {offd.nnz}; entries changed by > 1e-12: {changed}; ||H'-H||_F/||H||_F = {sps.linalg.norm(Dm)/sps.linalg.norm(H):.4f};"
        f" diagonal unchanged: {np.allclose(H.diagonal(), H2.diagonal())}; links no longer in Q8: {sum(q8label(C)=='other' for C in L2[:2000])}/2000 of the first 2000")
    # a Q8-valued connection is not a gauge invariant: how many of the transformed links are still in Q8
    t0 = time.time(); w1 = sla.eigvalsh(H.toarray(), overwrite_a=True, check_finite=False); t1 = time.time() - t0
    w2 = sla.eigvalsh(H2.toarray(), overwrite_a=True, check_finite=False); t2 = time.time() - t0 - t1
    log(f"   dense spectra computed ({t1:.0f}s, {t2:.0f}s): max|lambda_i - lambda'_i| = {np.abs(w1 - w2).max():.2e}  (machine precision ~ {np.finfo(float).eps*np.abs(w1).max():.1e} x spectral radius)")
    log(f"   lowest 8 (original)   : {np.array2string(w1[:8], precision=8, max_line_width=220)}")
    log(f"   lowest 8 (gauge-trans): {np.array2string(w2[:8], precision=8, max_line_width=220)}")
    log(f"   mean eigenvalue {w1.mean():.6f} (= 24 by the trace), max {w1.max():.6f}, Kramers pairing max|lambda_(2j+1)-lambda_(2j)| = {np.abs(w1[1::2]-w1[0::2]).max():.2e}")
    out = dict(n=n, dim=int(H.shape[0]), max_dev_H_vs_UHU=float(dev), offdiag_nnz=int(offd.nnz), entries_changed=changed,
               rel_frobenius_change=float(sps.linalg.norm(Dm) / sps.linalg.norm(H)), max_spectrum_diff=float(np.abs(w1 - w2).max()),
               lowest8_original=w1[:8].tolist(), lowest8_gauge=w2[:8].tolist(), mean=float(w1.mean()), max=float(w1.max()),
               kramers_max_split=float(np.abs(w1[1::2] - w1[0::2]).max()))
    p = os.path.join(RES, 'level4_clifford_pinned_eigs.npy')
    if os.path.exists(p):
        ref = np.load(p); out['max_diff_vs_phase5_dense'] = float(np.abs(ref - w1).max())
        log(f"   check vs phase-5 saved dense level-4 pinned spectrum: max|diff| = {out['max_diff_vs_phase5_dense']:.2e}")
    ch = jload('chair_clifford')
    if ch:
        r4 = [r for r in ch['records'] if r['level'] == 4]
        if r4:
            out['max_diff_lobpcg_vs_dense_lowest8'] = float(np.abs(np.array(r4[0]['eigenvalues']) - w1[:8]).max())
            log(f"   check LOBPCG level-4 lowest 8 (part chair clifford) vs dense: max|diff| = {out['max_diff_lobpcg_vs_dense_lowest8']:.2e}")
    np.save(os.path.join(RES, 'phase5a_level4_pinned_dense_eigs.npy'), w1); jdump(out, 'gauge')

# ---------------------------------------------------------------- part: Robin boundary conditions
def part_robin():
    log = Log('robin'); log("=== Robin-type diagonals d_a = deg_a + t (24 - deg_a) on the FR30 chair (t=0 free, t=1 pinned) ===")
    out = dict(convention='d_a = deg_a + t (24 - deg_a); boundary weight = ground-state tile weight on tiles with deg < 24', t_grid=ROBIN_T, levels={})
    for level in (3, 4):
        tiles, edges, deg = chair(FR30, level); n = len(tiles); links = clifford_links(tiles, edges)
        lv = dict(records=[], boundary_tile_fraction=float((deg < 24).mean()))
        pinned_ref = None
        def at(t):
            rec, H, V = run(f'chair/FR30/robin t={t:.5f}', n, edges, deg, links, deg + t * (24 - deg), 24, level, 8, log, k_solve=10)
            rec['t'] = float(t)
            if 'full_spectrum' in rec:
                full = rec.pop('full_spectrum'); rec['n_below_pinned_bottom'] = None; rec['_full'] = full
            lv['records'].append(rec); return rec
        rows = [at(t) for t in ROBIN_T]
        pin = rows[-1]['eigenvalues'][0]; free = rows[0]['eigenvalues'][0]
        if level == 3:
            for r in rows:
                if '_full' in r: r['n_below_pinned_bottom'] = int((r.pop('_full') < pin - 1e-9).sum())
        # bisection on the first downward crossing of boundary weight 0.5
        lo = hi = None
        for r1, r2 in zip(rows, rows[1:]):
            if r1['boundary_weight'] > 0.5 >= r2['boundary_weight']: lo, hi = r1['t'], r2['t']; break
        if lo is not None:
            for _ in range(6):
                mid = 0.5 * (lo + hi); r = at(mid); r.pop('_full', None)
                if r['boundary_weight'] > 0.5: lo = mid
                else: hi = mid
            lv['t_star_boundary_weight_half'] = [lo, hi]
        for r in lv['records']: r.pop('_full', None)
        lv['records'].sort(key=lambda r: r['t'])
        log(f"\n   level {level} summary (boundary tile fraction {lv['boundary_tile_fraction']:.3f}; free bottom {free:.5f}, pinned bottom {pin:.5f}):")
        log(f"   {'t':>8} {'lambda_min':>11} {'lambda_2nd pair':>15} {'bw':>7} {'IPR*n':>8} {'s50':>6} {'#<pinned(l3)':>13}")
        for r in lv['records']:
            nb = r.get('n_below_pinned_bottom'); nbs = f"{nb:13d}" if nb is not None else f"{'-':>13}"
            log(f"   {r['t']:8.5f} {r['eigenvalues'][0]:11.6f} {r['eigenvalues'][2]:15.6f} {r['boundary_weight']:7.4f} {r['ipr_n']:8.3f} {r['s50']:6d} {nbs}")
        if lo is not None: log(f"   boundary weight crosses 1/2 between t = {lo:.5f} and {hi:.5f}")
        out['levels'][str(level)] = lv
    jdump(out, 'robin')

# ---------------------------------------------------------------- part: unit-cube (periodic geometry) control
def part_cube(maxlevel):
    log = Log('cube'); dec = {v: FR30.get(v, (0, 2, 1)) for v in V8}
    log("=== unit-cube block substitution control (8 octant children at corners v, frames D_s(v) P(pi_v), FR30-type decoration, (1,1,1) -> odd (0,2,1)); unit-cube tiles, bulk coordination 6, pinned diagonal 6 ===")
    log("   decoration: " + ', '.join(f"{v}:{dec[v]}" for v in V8))
    for name in ('fr30type', 'trivial'):
        out = dict(name=name, decoration={str(k): list(v) for k, v in dec.items()}, records=[])
        for level in range(3, maxlevel + 1):
            tiles = cube_tiles(dec, level); owner, edges = panel_edges(tiles); n = len(tiles); deg = degrees(n, edges); assert deg.max() == 6
            links = clifford_links(tiles, edges) if name == 'fr30type' else [I2] * len(edges)
            if name == 'fr30type' and level == 3: log(f"   link labels: {dict(collections.Counter(q8label(C) for C in links))}")
            rec, H, V = run(f'cube/{name}/pinned6', n, edges, deg, links, np.full(n, 6.0), 6, level, 8 if level <= 4 else 6, log)
            if name == 'trivial':
                Lb = 2**level; ex = 6 - 6 * np.cos(np.pi / (Lb + 1)); exipr = (1.5 * Lb / (Lb + 1))**3
                rec['exact_lambda0'] = float(ex); rec['exact_ipr_n'] = float(exipr)
                log(f"   exact Dirichlet box: lambda_0 = 6 - 6 cos(pi/(L+1)) = {ex:.9f} (diff {rec['eigenvalues'][0]-ex:+.1e}); exact IPR*n = (1.5 L/(L+1))^3 = {exipr:.5f} (diff {rec['ipr_n']-exipr:+.1e})")
            out['records'].append(rec)
        scaling(out, log); strip_full(out); jdump(out, f'cube_{name}')

# ---------------------------------------------------------------- part: merge and comparison table
def part_table():
    log = Log('table'); merged = dict(conventions=__doc__, parts={})
    rows = []
    def row(name, out):
        if not out: return
        merged['parts'][name] = out
        rec = {r['level']: r for r in out['records']}; sc = {tuple(s['levels']): s for s in out.get('scaling', [])}
        rows.append((name, rec, sc))
    row('FR30 Clifford (pinned)', jload('chair_clifford')); row('FR30 graph, trivial links', jload('chair_trivial'))
    row('FR30 sign-stripped (adjoint-only)', jload('chair_stripped')); row('FR30 graph, random i.i.d. Q8', jload('chair_randq8'))
    for i in range(6): row(f'random admissible decoration #{i}', jload(f'randdec{i}'))
    row('unit cube / FR30-type decoration (pinned 6)', jload('cube_fr30type')); row('unit cube / trivial links (pinned 6)', jload('cube_trivial'))
    for tag in ('perturb', 'gauge', 'robin'):
        o = jload(tag)
        if o: merged['parts'][tag] = o
    def f(x, w=9, p=5): return f"{x:{w}.{p}f}" if x is not None else f"{'-':>{w}}"
    log("COMPARISON TABLE (pinned lowest eigenvalue; tile IPR*n of the Kramers ground pair; gamma from IPR ~ n^-gamma between levels; extended -> gamma 1, IPR*n const; localized -> gamma 0)")
    hdr = f"{'model':<46} {'bottom L3':>9} {'bottom L4':>9} {'bottom L5':>9} | {'IPR*n L3':>8} {'IPR*n L4':>8} {'IPR*n L5':>8} | {'g(3->4)':>7} {'g(4->5)':>7} | {'bw L4':>6} {'max res':>8}"
    log(hdr); log('-' * len(hdr))
    for name, rec, sc in rows:
        b = [rec[l]['eigenvalues'][0] if l in rec else None for l in (3, 4, 5)]
        ip = [rec[l]['ipr_n'] if l in rec else None for l in (3, 4, 5)]
        g = [sc[(3, 4)]['gamma'] if (3, 4) in sc else None, sc[(4, 5)]['gamma'] if (4, 5) in sc else None]
        bw4 = rec[4]['boundary_weight'] if 4 in rec else None; mr = max(max(r['residuals']) for r in rec.values())
        log(f"{name:<46} {f(b[0])} {f(b[1])} {f(b[2])} | {f(ip[0],8,3)} {f(ip[1],8,3)} {f(ip[2],8,3)} | {f(g[0],7,3)} {f(g[1],7,3)} | {f(bw4,6,3)} {mr:8.1e}")
    merged['table_rows'] = [dict(model=name, bottom={l: rec[l]['eigenvalues'][0] for l in rec}, ipr_n={l: rec[l]['ipr_n'] for l in rec},
                                 gamma={f"{a}->{b}": s['gamma'] for (a, b), s in sc.items()}, boundary_weight={l: rec[l]['boundary_weight'] for l in rec},
                                 max_residual=max(max(r['residuals']) for r in rec.values())) for name, rec, sc in rows]
    log("\nLOWEST 8 PINNED EIGENVALUES (levels 3, 4) AND LOWEST 6 (level 5)")
    for name, rec, sc in rows:
        for l in sorted(rec):
            r = rec[l]; log(f"  {name:<46} L{l}: {np.array2string(np.array(r['eigenvalues']), precision=5, max_line_width=220)}  max res {max(r['residuals']):.1e}  [{r['solver']}, {r['seconds']:.0f}s]")
    for tag, title in (('perturb', 'COUPLING PERTURBATIONS'), ('gauge', 'GAUGE EQUIVALENCE'), ('robin', 'ROBIN BOUNDARY CONDITIONS')):
        p = os.path.join(RES, f'phase5a_controls_{tag}.txt')
        if os.path.exists(p): log(f"\n{title} (from phase5a_controls_{tag}.txt)\n" + open(p).read())
    with open(os.path.join(RES, 'phase5a_controls.json'), 'w') as fh: json.dump(merged, fh, indent=1, default=conv)
    os.replace(os.path.join(RES, 'phase5a_controls_table.txt'), os.path.join(RES, 'phase5a_controls.txt'))

if __name__ == '__main__':
    part = sys.argv[1]
    if part == 'chair': part_chair(sys.argv[2], int(sys.argv[3]) if len(sys.argv) > 3 else 5)
    elif part == 'randdec': part_randdec([int(x) for x in sys.argv[2:]] or list(range(6)))
    elif part == 'perturb': part_perturb()
    elif part == 'gauge': part_gauge()
    elif part == 'robin': part_robin()
    elif part == 'cube': part_cube(int(sys.argv[2]) if len(sys.argv) > 2 else 5)
    elif part == 'table': part_table()
    else: raise SystemExit(__doc__)
