#!/usr/bin/env python3
"""Phase V-D: nonlocal spectral recursion -- effective boundary (Schur-complement) operators of supertiles.

OPERATOR.  H = 24 I - A on l^2(tiles) x C^2 for a level-L patch (pinned; Phase V-A conventions, phase5a_controls.build_H).
Because the diagonal is 24 on EVERY tile, for a level-L supertile with depth-1 children c = 0..7 (tile index // 8^(L-1))
    H(T_L) = (+)_c H_pin(child c)  -  V,      V = inter-child panel hoppings,                                   (1)
where H_pin(child c) is literally the pinned operator of the child in its own tile order (links are rotation-invariant).

PARTITION.  Surface of child c: S_c = tiles of child c with at least one of their 24 panel neighbours outside child c
(another child, or missing).  Interior I_c = the rest.  Every inter-child hop joins two surface tiles, so with
S = U S_c, I = U I_c, H_II = (+)_c H_{I_c I_c} is block diagonal.  For E below lambda_min(H_II) (ADMISSIBLE ENERGIES):
    child response   R_c(E) = H_{S_c S_c} - E - H_{S_c I_c} (H_{I_c I_c} - E)^{-1} H_{I_c S_c}
    glued operator   K(E)   = (+)_c R_c(E) - V_SS  = Schur complement of H - E onto S.                             (2)
SCHUR CRITERION (Theorem D1, proved in the report): det(H - E) = det(H_II - E) det K(E); for E < lambda_min(H_II),
H_II - E > 0, K(E) is Hermitian with dK/dE = -I - X^dag X <= -I (X = (H_II - E)^{-1} H_IS), so lambda_min(K(E)) is strictly
decreasing with slope <= -1, and lambda_min(H) is the unique root of lambda_min(K(E)) = 0 provided that root is below
lambda_min(H_II).  RECURSION (Theorem D2): applying (2) inside each child, R for T_L is the Schur complement of the glued
operator built from the children's surface responses onto the parent's own surface -- exact, no truncation.
REDUCED ORDER: P_k = (+)_c (k lowest eigenvectors of R_c(E)); g_k(E) = lambda_min(P_k^dag K(E) P_k) >= lambda_min(K(E))
(Rayleigh-Ritz), an 8k-mode interface model with a one-sided error.

FROZEN DESCRIPTORS (protocol fixed in audit/results/phase5d_protocol.json before any held-out evaluation):
    at fixed energies E in {6.0, 7.0, 8.0} (admissibility recorded per rule):
    c1(E)  = mean_c lambda_min(R_c(E))                        child surface response alone (no gluing)
    g_k(E) = lambda_min(P_k^dag K(E) P_k), k = 1, 2, 4, 8 Kramers pairs per child (degenerate multiplets completed) reduced interface models
    gp_k(E) = g_k(E) - c1(E)                                   gluing penalty
    kmin(E) = lambda_min(K(E))                                 EXACT REFORMULATION (control for the method; excluded from
                                                                mechanism claims because its root IS the target)
Usage: python3 -u -I audit/phase5d_schur.py validate | recursion | features <shard> <nshards> | controls | analyze
"""
import os, sys, time, json, collections, resource
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
RES = os.path.join(HERE, 'results')
import numpy as np, scipy.sparse as sps, scipy.linalg as sla, scipy.sparse.linalg as spl
from independent_clifford_q8_audit import FR30, tiles_at_level, panel_edges
from phase5a_controls import clifford_links, build_H, degrees
import phase5b_sweep as sw

EGRID = (6.0, 7.0, 8.0); KS = (1, 2, 4, 8)          # k = number of KRAMERS PAIRS kept per child (2k vectors, multiplets completed)
def log(*a): print(*a, flush=True)
def rss(): return resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 1e6

# ------------------------------------------------------------------ construction
def build(tiles):
    _, edges = panel_edges(tiles); n = len(tiles)
    links = clifford_links(tiles, edges); H = build_H(n, edges, links, np.full(n, 24.0))
    return H.tocsr(), edges

def spinor(idx): idx = np.asarray(idx); return np.ravel(np.c_[2 * idx, 2 * idx + 1])

def partition(n, edges, level, depth=1):
    """children by depth-`depth` ancestor; surface = tiles with a neighbour outside their child (or missing)."""
    child = np.arange(n) // 8 ** (level - depth)
    a = np.array([e[0] for e in edges]); b = np.array([e[1] for e in edges])
    deg_in = np.zeros(n, int); same = child[a] == child[b]
    np.add.at(deg_in, a[same], 1); np.add.at(deg_in, b[same], 1)
    surf = deg_in < 24
    return child, surf

class Glued:
    def __init__(self, H, child, surf):
        self.H = H.tocsr(); self.child = child; self.surf = surf
        self.kids = sorted(set(child.tolist()))
        self.S = [np.nonzero((child == c) & surf)[0] for c in self.kids]
        self.I = [np.nonzero((child == c) & ~surf)[0] for c in self.kids]
        self.Sall = np.concatenate(self.S); self.sS = spinor(self.Sall)
        self.offs = np.cumsum([0] + [2 * len(s) for s in self.S])
        self.blocks = []
        for s, i in zip(self.S, self.I):
            ss, ii = spinor(s), spinor(i)
            self.blocks.append((self.H[ss][:, ss].toarray(), self.H[ss][:, ii].toarray(), self.H[ii][:, ii].toarray()))
        self.HSS = self.H[self.sS][:, self.sS].toarray()
        self.lam_II = min(float(sla.eigvalsh(B[2], subset_by_index=(0, 0))[0]) if B[2].shape[0] else np.inf for B in self.blocks)
    def R(self, E):
        out = []
        for HSS, HSI, HII in self.blocks:
            if HII.shape[0]: X = sla.solve(HII - E * np.eye(HII.shape[0]), HSI.conj().T, assume_a='her'); out.append(HSS - E * np.eye(HSS.shape[0]) - HSI @ X)
            else: out.append(HSS - E * np.eye(HSS.shape[0]))
        return out
    def K(self, E, Rs=None):
        Rs = self.R(E) if Rs is None else Rs; K = self.HSS - E * np.eye(self.HSS.shape[0])
        for c, Rc in enumerate(Rs):
            o0, o1 = self.offs[c], self.offs[c + 1]; K[o0:o1, o0:o1] = Rc
        return K
    def lam_min(self, M, k=1):
        if M.shape[0] <= 1200: return sla.eigvalsh(M, subset_by_index=(0, k - 1))
        w = spl.eigsh(M, k=max(k, 2), which='SA', tol=1e-12, v0=np.ones(M.shape[0], complex), ncv=60, maxiter=20000, return_eigenvectors=False)
        return np.sort(w)[:k]
    def features(self, E):
        Rs = self.R(E); K = self.K(E, Rs)
        evs = [sla.eigh(Rc) for Rc in Rs]
        c1 = float(np.mean([w[0] for w, _ in evs]))
        out = {'E': E, 'admissible': bool(E < self.lam_II), 'lam_II': self.lam_II, 'c1': c1, 'c1_min': float(min(w[0] for w, _ in evs)),
               'kmin': float(self.lam_min(K)[0])}
        for k in KS:
            cols = []
            for c, (w, U) in enumerate(evs):
                m = min(2 * k, len(w))
                while m < len(w) and w[m] - w[m - 1] < 1e-8: m += 1      # never split a degenerate multiplet (gauge invariance)
                blk = np.zeros((K.shape[0], m), complex); blk[self.offs[c]:self.offs[c + 1], :] = U[:, :m]; cols.append(blk)
            P = np.hstack(cols)
            g = float(np.linalg.eigvalsh(P.conj().T @ K @ P)[0]); out[f'g{k}'] = g; out[f'gp{k}'] = g - c1; out[f'dim{k}'] = int(P.shape[1])
        return out
    def root(self, lo, hi, tol=1e-10, fn=None):
        f = fn or (lambda E: self.lam_min(self.K(E))[0])
        flo, fhi = f(lo), f(hi); it = 0
        assert flo > 0 > fhi, (lo, hi, flo, fhi)
        while hi - lo > tol and it < 200:                       # safeguarded secant/bisection on a decreasing function
            m = hi - fhi * (hi - lo) / (fhi - flo)
            if not (lo < m < hi) or it % 3 == 2: m = 0.5 * (lo + hi)
            fm = f(m); it += 1
            if fm > 0: lo, flo = m, fm
            else: hi, fhi = m, fm
        return 0.5 * (lo + hi), it

def tiles_of(spec, level):
    if isinstance(spec, dict): return tiles_at_level(spec, level)
    if isinstance(spec, int): return tiles_at_level(sw.decoration(spec), level)
    import phase5b_controls as pc
    return pc.system_tiles(spec, level)[0]

# ------------------------------------------------------------------ validation
def validate():
    rows = []
    for L in (2, 3):
        for spec in (FR30, 2238, 'iid1', 'shuffle1'):
            t0 = time.time(); tiles = tiles_of(spec, L); H, edges = build(tiles); child, surf = partition(len(tiles), edges, L)
            G = Glued(H, child, surf); w = np.linalg.eigvalsh(H.toarray())
            E0 = w[0]; hi = min(G.lam_II - 1e-6, E0 + 0.5); E0s, it = G.root(E0 - 1.0, hi) if E0 < G.lam_II else (np.nan, 0)
            # count criterion: # eigenvalues of H below e equals # negative eigenvalues of K(e) for e < lam_II (Sylvester / Haynsworth inertia)
            checks = []
            for e in np.linspace(E0 - 0.5, min(G.lam_II - 1e-3, E0 + 2.0), 7):
                nH = int((w < e).sum()); nK = int((np.linalg.eigvalsh(G.K(e)) < 0).sum()); checks.append((round(float(e), 4), nH, nK))
            # gauge: random SU(2) per tile
            rng = np.random.default_rng(7); n = len(tiles); Us = []
            for _ in range(n):
                q = rng.normal(size=4); q /= np.linalg.norm(q); Us.append(np.array([[q[0] + 1j * q[3], q[2] + 1j * q[1]], [-q[2] + 1j * q[1], q[0] - 1j * q[3]]]))
            Gm = sps.block_diag(Us, format='csr'); Hg = (Gm @ H @ Gm.conj().T).tocsr()
            Gg = Glued(Hg, child, surf); Ef = 0.5 * (E0 + min(G.lam_II, E0 + 1)) - 0.3
            f1, f2 = G.features(Ef), Gg.features(Ef)
            gdev = max(abs(f1[k] - f2[k]) for k in f1 if k not in ('E', 'admissible', 'lam_II') and not k.startswith('dim'))
            rec = {'level': L, 'system': spec if not isinstance(spec, dict) else 'fr30', 'E0_direct': float(E0), 'E0_schur': float(E0s), 'iterations': it,
                   'abs_err': float(abs(E0 - E0s)), 'lam_II': G.lam_II, 'surface_tiles': int(surf.sum()), 'inertia_checks': checks,
                   'inertia_ok': all(a == b for _, a, b in checks), 'gauge_max_dev': float(gdev), 'seconds': time.time() - t0}
            rows.append(rec)
            log(f"[validate L{L} {rec['system']}] E0 direct {E0:.12f}  Schur root {E0s:.12f}  |err| {rec['abs_err']:.1e} ({it} it)  lam_min(H_II) {G.lam_II:.5f}  "
                f"surface {rec['surface_tiles']}/{n}  inertia {'OK' if rec['inertia_ok'] else checks}  gauge dev {gdev:.1e}")
    json.dump(rows, open(os.path.join(RES, 'phase5d_validate.json'), 'w'), indent=1)

# ------------------------------------------------------------------ recursion across levels
def recursion(maxL=4, E=7.0, specs=(('fr30', FR30), ('dec3697', 3697), ('dec1387', 1387), ('dec2238', 2238))):
    """R_m(E) of the full supertile surface, (a) directly from H(T_m) and (b) by the exact recursion from 8 child copies of
    R_{m-1}(E) and the inter-child hoppings; plus the low spectrum of R_m(E) across m (spectral flow across levels)."""
    out = {}
    for name, spec in specs:
        recs = []; Rprev = None
        for m in range(1, maxL + 1):
            t0 = time.time(); tiles = tiles_of(spec, m); H, edges = build(tiles); n = len(tiles)
            deg = degrees(n, edges); surf_m = deg < 24                            # surface of the whole supertile
            # (a) direct Schur onto the supertile surface
            s, i = np.nonzero(surf_m)[0], np.nonzero(~surf_m)[0]; ss, ii = spinor(s), spinor(i)
            Hd = H.toarray(); HSS, HSI, HII = Hd[np.ix_(ss, ss)], Hd[np.ix_(ss, ii)], Hd[np.ix_(ii, ii)]
            Rdir = HSS - E * np.eye(len(ss)) - (HSI @ sla.solve(HII - E * np.eye(len(ii)), HSI.conj().T, assume_a='her') if len(ii) else 0)
            rec = {'m': m, 'surface_tiles': int(surf_m.sum()), 'dim_R': int(len(ss)), 'lam_II': float(sla.eigvalsh(HII, subset_by_index=(0, 0))[0]) if len(ii) else None}
            if Rprev is not None:
                # (b) recursion: children are copies of T_{m-1}; child surface (whole-child surface) responses = Rprev
                child = np.arange(n) // 8 ** (m - 1); nc = n // 8
                dprev = Rprev['deg']; sp = np.nonzero(dprev < 24)[0]                    # surface tiles of T_{m-1} in its own order
                Sglob = np.concatenate([c * nc + sp for c in range(8)]); sg = spinor(Sglob)
                Kc = Hd[np.ix_(sg, sg)] - E * np.eye(len(sg)); blk = len(spinor(sp))
                for c in range(8): Kc[c * blk:(c + 1) * blk, c * blk:(c + 1) * blk] = Rprev['R']
                # Schur of the glued child-surface operator onto the parent surface (subset of child surfaces)
                pos = {t: k for k, t in enumerate(Sglob)}
                keep = np.array([pos[t] for t in s]); drop = np.setdiff1d(np.arange(len(Sglob)), keep)
                kk, dd = spinor(keep), spinor(drop)
                Rrec = Kc[np.ix_(kk, kk)] - Kc[np.ix_(kk, dd)] @ sla.solve(Kc[np.ix_(dd, dd)], Kc[np.ix_(dd, kk)], assume_a='her')
                rec['recursion_max_abs_dev'] = float(np.abs(Rrec - Rdir).max())
            w = sla.eigvalsh(Rdir); rec['R_low'] = w[:8].tolist(); rec['R_neg_count'] = int((w < 0).sum()); rec['seconds'] = time.time() - t0
            log(f"[recursion {name} m={m}] surface {rec['surface_tiles']} dim {rec['dim_R']}  lowest R_m({E}) {np.round(w[:4],4)}  #neg {rec['R_neg_count']}  "
                f"recursion dev {rec.get('recursion_max_abs_dev', float('nan')):.1e}  ({rec['seconds']:.0f}s)")
            recs.append(rec); Rprev = {'R': Rdir, 'deg': deg}
        out[name] = recs
    json.dump(out, open(os.path.join(RES, 'phase5d_recursion.json'), 'w'), indent=1)

# ------------------------------------------------------------------ features for rules and controls
def feature_record(spec, level=4, E0_known=None, solve_root=False):
    t0 = time.time(); tiles = tiles_of(spec, level); H, edges = build(tiles); child, surf = partition(len(tiles), edges, level)
    G = Glued(H, child, surf); rec = {'surface_tiles': int(surf.sum()), 'lam_II': G.lam_II, 'feat': [G.features(E) for E in EGRID]}
    if solve_root and E0_known is not None and E0_known < G.lam_II:
        r, it = G.root(E0_known - 0.05, min(G.lam_II - 1e-6, E0_known + 0.05)); rec['E0_schur'] = r; rec['E0_err'] = abs(r - E0_known)
    rec['seconds'] = time.time() - t0; rec['rss_gb'] = rss()
    return rec

def class_key(r):
    p = r['pred']; return (round(r['L3']['lambda'][0], 7), p['n_plus'], p['n_minus'], tuple(sorted((p['n_i'], p['n_j'], p['n_k']))))

def dataset():
    D = json.load(open(os.path.join(RES, 'phase5b_sweep.json'))); R = D['records']; by = {r['index']: r for r in R}
    top = json.load(open(os.path.join(RES, 'phase5c_top_level3_at_level4.json')))
    for t in top:
        r = by[t['index']]
        if 'L4' not in r: r['L4'] = {'lambda': [t['Y4']], 'residual': t['res4'], 'source': 'phase5c_top_level3_at_level4.json'}
    seen = {}
    for r in R:
        if 'L4' in r:
            k = class_key(r)
            if k not in seen or r['is_fr30']: seen[k] = r
    return sorted(seen.values(), key=lambda r: r['index'])

def run_features(shard, nshards):
    rules = dataset(); path = os.path.join(RES, f'phase5d_features_shard{shard}.jsonl'); done = set()
    if os.path.exists(path):
        for l in open(path):
            try: done.add(json.loads(l)['index'])
            except json.JSONDecodeError: pass
    todo = [r for j, r in enumerate(rules) if j % nshards == shard and r['index'] not in done]
    log(f"[features shard {shard}/{nshards}] {len(todo)} rule classes to do ({len(done)} done) of {len(rules)}")
    with open(path, 'a') as f:
        for j, r in enumerate(todo):
            rec = feature_record(r['index'], 4, r['L4']['lambda'][0], solve_root=(r['is_fr30'] or j % 25 == 0))
            rec.update({'index': r['index'], 'is_fr30': r['is_fr30'], 'Y4': r['L4']['lambda'][0], 'Y3': r['L3']['lambda'][0]})
            f.write(json.dumps(rec) + '\n'); f.flush()
            if j % 10 == 0: log(f"  {j}/{len(todo)} idx {r['index']}: kmin(7)={rec['feat'][1]['kmin']:+.4f} g1(7)={rec['feat'][1]['g1']:+.4f} c1(7)={rec['feat'][1]['c1']:+.4f} "
                                f"lamII {rec['lam_II']:.3f} {('E0err %.1e' % rec['E0_err']) if 'E0_err' in rec else ''} ({rec['seconds']:.0f}s, {rec['rss_gb']:.2f} GB)")

CONTROLS = ['fr30', 'iid1', 'iid2', 'iid3', 'coarse1', 'coarse2', 'coarse3', 'fine1', 'fine2', 'fine3', 'shuffle1', 'shuffle2', 'shuffle3',
            'flip1,0.05', 'flip2,0.05', 'flip1,0.2', 'dec2238', 'dec2159']
def run_controls():
    ctl = {json.loads(l)['system']: json.loads(l) for l in open(os.path.join(RES, 'phase5b_controls.jsonl')) if json.loads(l)['level'] == 4}
    path = os.path.join(RES, 'phase5d_controls.jsonl')
    with open(path, 'w') as f:
        for name in CONTROLS:
            spec = FR30 if name == 'fr30' else (int(name[3:]) if name.startswith('dec') else name)
            c = ctl[name]; rec = feature_record(spec, 4, c['lambda'][0], solve_root=True)
            rec.update({'system': name, 'Y4': c['lambda'][0], 'f_trl': c['pred']['f_trl'], 'f_m1': c['pred']['f_m1']})
            f.write(json.dumps(rec) + '\n'); f.flush()
            log(f"[control {name}] Y4 {c['lambda'][0]:.5f}  E0 via Schur {rec.get('E0_schur', float('nan')):.6f} (err {rec.get('E0_err', float('nan')):.1e})  "
                f"g1(7) {rec['feat'][1]['g1']:+.4f}  c1(7) {rec['feat'][1]['c1']:+.4f}  gp1(7) {rec['feat'][1]['gp1']:+.4f}  ({rec['seconds']:.0f}s)")

if __name__ == '__main__':
    os.environ.setdefault('OMP_NUM_THREADS', '2')
    cmd = sys.argv[1]
    if cmd == 'validate': validate()
    elif cmd == 'recursion': recursion(int(sys.argv[2]) if len(sys.argv) > 2 else 4)
    elif cmd == 'features': run_features(int(sys.argv[2]), int(sys.argv[3]))
    elif cmd == 'controls': run_controls()
