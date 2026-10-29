#!/usr/bin/env python3
"""Phase XIV, first dynamical experiment: the Chair44 matter floor in a dynamical Q8 gauge ensemble on the chair hull.

Protocol frozen in audit/results/phase14_preregistration_dynamical.json (commit 429d370) before any value was computed.
Gauge field: the Phase V-C engine G (audit/phase5c_q8_gauge.py) unchanged, on fr30_complex(3): dual cubical complex of the
pinned level-3 chair supertile, rigid tiles (intra-tile links = 1), Wilson action beta sum_p (1 - (1/2) Re Tr U_p).
Matter: H_U = 24 - sum_l [L(U_l) at (own x, own x+mu) + transpose], L(q) = real 4x4 left multiplication by the quaternion q;
lambda_min(H_U) by dense eigvalsh.  [E]: a Monte Carlo ensemble on one finite patch; nothing here is a physical claim.
Usage: python -u -I audit/phase14_dynamical.py [checks|run] -> audit/results/phase14_dynamical.json"""
import os, sys, json, time
os.environ.setdefault('OMP_NUM_THREADS', '1')
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); RES = os.path.join(HERE, 'results')
import numpy as np
import phase5c_q8_gauge as G5
from independent_clifford_q8_audit import FR30, tiles_at_level

PROTO = json.load(open(os.path.join(RES, 'phase14_preregistration_dynamical.json')))
LEVEL = 3

def lmat(q):
    """4x4 real matrix of left multiplication x -> q x on quaternions (w, x, y, z)"""
    a, b, c, d = q
    return np.array([[a, -b, -c, -d], [b, a, -d, c], [c, d, a, -b], [d, -c, b, a]], float)
LM = np.array([lmat(G5.QV[g]) for g in range(8)])

class Hull:
    def __init__(self, level=LEVEL):
        self.nl, self.plaq, self.frozen, self.inter = G5.fr30_complex(level)
        tiles = tiles_at_level(FR30, level); N = 2 ** (level + 1)
        own = -np.ones((N, N, N), int)
        for a, (_, _, cs) in enumerate(tiles):
            for c in cs: own[c] = a
        self.n = len(tiles)
        # rebuild the link list exactly as fr30_complex does, to know each link's two tiles
        E = np.eye(3, dtype=int); ends = []
        for x in [tuple(x) for x in np.argwhere(own >= 0)]:
            for mu in range(3):
                y = tuple(np.array(x) + E[mu])
                if all(0 <= v < N for v in y) and own[y] >= 0: ends.append((own[x], own[y]))
        assert len(ends) == self.nl
        self.ends = np.array(ends); self.dyn = np.nonzero(~self.frozen)[0]
        assert all(self.ends[l, 0] != self.ends[l, 1] for l in self.dyn) and all(self.ends[l, 0] == self.ends[l, 1] for l in np.nonzero(self.frozen)[0])

    def H(self, U):
        H = 24.0 * np.eye(4 * self.n)
        for l in self.dyn:
            a, b = self.ends[l]; M = LM[U[l]]
            H[4 * a:4 * a + 4, 4 * b:4 * b + 4] -= M; H[4 * b:4 * b + 4, 4 * a:4 * a + 4] -= M.T
        return H

    def floor(self, U): return float(np.linalg.eigvalsh(self.H(U))[0])

    def gauge(self, U, g):
        """U_l -> g_(own x) U_l g_(own x+mu)^-1 on every link (frozen links stay 1 because both ends are one tile)"""
        a, b = self.ends[:, 0], self.ends[:, 1]
        return G5.MUL[G5.MUL[g[a], U], G5.INV[g[b]]]

def checks():
    hull = Hull(); out = {'links': int(hull.nl), 'dynamical_links': int(len(hull.dyn)), 'plaquettes': int(len(hull.plaq)),
                          'inter_tile_plaquettes': int(hull.inter.sum()), 'tiles': hull.n}
    U1 = np.zeros(hull.nl, np.int8); f1 = hull.floor(U1)
    out['C1_trivial_floor'] = f1; out['C1_passes'] = abs(f1 - 1.66951) < 1e-5
    rng = np.random.default_rng(7); U = rng.integers(0, 8, hull.nl).astype(np.int8); U[hull.frozen] = 0
    f = hull.floor(U); dev = []
    for _ in range(3):
        g = rng.integers(0, 8, hull.n).astype(np.int8); dev.append(abs(hull.floor(hull.gauge(U, g)) - f))
    out['C2_gauge_covariance_max_dev'] = float(max(dev)); out['C2_passes'] = max(dev) < 1e-9
    return out, hull

def run(hull, beta, start, seed, ntherm, nmeas, every):
    eng = G5.General(hull.nl, hull.plaq, hull.frozen, seed=seed)
    if start == 'hot':
        eng.U = eng.rng.integers(0, 8, hull.nl).astype(np.int8); eng.U[hull.frozen] = 0
    else:
        eng.U = np.zeros(hull.nl, np.int8)
    for _ in range(ntherm): eng.sweep(beta)
    P, V, Fl, counts = [], [], [], np.zeros(8)
    for _ in range(nmeas):
        for _ in range(every): eng.sweep(beta)
        g = eng.plaquettes()[hull.inter]; P.append(float(G5.RE[g].mean())); V.append(float((g == 1).mean()))
        Fl.append(hull.floor(eng.U)); counts += np.bincount(eng.U[hull.dyn], minlength=8)
    se = lambda a: float(np.std(a, ddof=1) / np.sqrt(len(a)))
    return {'beta': beta, 'start': start, 'seed': seed, 'P_inter': float(np.mean(P)), 'P_err': se(P),
            'minus_one_density': float(np.mean(V)), 'floor_mean': float(np.mean(Fl)), 'floor_err': se(Fl),
            'floor_min': float(np.min(Fl)), 'floor_max': float(np.max(Fl)), 'floors': Fl,
            'link_frequencies': (counts / counts.sum()).tolist()}

if __name__ == '__main__':
    cmd = sys.argv[1] if len(sys.argv) > 1 else 'run'
    path = os.path.join(RES, 'phase14_dynamical.json')
    t0 = time.time(); ck, hull = checks(); print('checks', ck, flush=True)
    out = {'protocol_sha256_note': 'phase14_preregistration_dynamical.json, commit 429d370', 'checks': ck, 'runs': []}
    if cmd == 'run':
        r = PROTO['run']; nth, nme, ev = 300, 40, 10
        for beta in r['betas']:
            for start, seed in (('hot', 0), ('cold', 1)):
                rec = run(hull, beta, start, seed, nth, nme, ev); out['runs'].append(rec)
                print({k: v for k, v in rec.items() if k not in ('floors', 'link_frequencies')}, f'[{time.time() - t0:.0f}s]', flush=True)
                json.dump(out, open(path, 'w'), indent=1)
    json.dump(out, open(path, 'w'), indent=1)
