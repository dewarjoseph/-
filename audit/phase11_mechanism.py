#!/usr/bin/env python3
"""Phase XI, Part V: why the leading rules are strong -- their weakest legal environments.

For a rule r: the legal 8-balls (Theorem XI.D enumeration, phase11_chair), the plain Dirichlet bottom of each (D_8 = minimum, an
upper bound on E_*) and the amplified bottom (Lambda_8 = minimum, a lower bound); the minimising balls, the 1-star type of their
centre tile, and gauge-invariant holonomy data of the centre (two-cycle and triangle angles) and of the ball (two-cycle class
counts and plaquette class counts inside the ball).
Cross-rule comparison is gauge-invariant: an environment's FINGERPRINT is (geometric configuration, Dirichlet spectrum rounded to
1e-8).  The geometry of every rule's tilings is the undecorated chair geometry (frames only relabel), so two rules' environments
on the same geometric configuration are comparable; equal fingerprints are necessary for gauge equivalence.
Usage: python -u -I audit/phase11_mechanism.py balls <rule> [R] [nproc]   -> audit/results/phase11_mechanism.json (merged by rule)
       python -u -I audit/phase11_mechanism.py compare                  -> the FR30 -> 4753 comparison and the census association"""
import os, sys, json, time, math, collections, types, hashlib
sys.modules.setdefault('resource', types.SimpleNamespace(getrusage=lambda *a: types.SimpleNamespace(ru_maxrss=0), RUSAGE_SELF=0))
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); RES = os.path.join(HERE, 'results')
import numpy as np
from fractions import Fraction
import phase11_chair as C, phase11_local as Lc
T0 = time.time()
def log(*a): print(f"[{time.time()-T0:7.0f}s]", *a, flush=True)
OUT = os.path.join(RES, 'phase11_mechanism.json')
def save(key, obj):
    d = json.load(open(OUT)) if os.path.exists(OUT) else {}
    d[key] = obj; json.dump(d, open(OUT, 'w'), indent=1, default=float)

PERM_MATS = [C.perm_matrix(p) for p in C.PERMS]
def shape_key(Grel, Trel):
    """the geometric configuration: relative positions and tile shapes (a tile's cube set is invariant under G -> G P, P a
    permutation matrix, because the chair is), canonicalised"""
    best = None
    for Q in PERM_MATS:                       # the centre tile's frame is defined only up to the chair's symmetry G -> G Q
        rows = []
        for G, T in zip(Grel.astype(np.int64), Trel.astype(np.int64)):
            Gq = Q.T @ G; g = min(tuple((Gq @ P).ravel().tolist()) for P in PERM_MATS); rows.append((g, tuple((Q.T @ T).tolist())))
        s = repr(sorted(rows))
        if best is None or s < best: best = s
    return hashlib.sha1(best.encode()).hexdigest()[:16]
def fingerprint(Grel, Trel):
    H = C.operators(Grel.astype(np.int64), Trel.astype(np.int64)); ev = np.linalg.eigvalsh(H.toarray())
    return shape_key(Grel, Trel), hashlib.sha1(np.round(ev, 8).tobytes()).hexdigest()[:16], float(ev[0])

def ball_holonomy(G, T):
    """two-cycle classes and plaquette (cube 4-cycle) classes inside a ball patch; centre loops"""
    G = G.astype(np.int64); T = T.astype(np.int64); P = C.Patch(G, T); a, b, k = P.panels(); U = C.link_matrices(G, a, b, k)
    def cls(W):
        tr = np.trace(W).real
        return '+1' if tr > 1.5 else '-1' if tr < -1.5 else 'traceless'
    pair = collections.defaultdict(list)
    for x, y, u in zip(a.tolist(), b.tolist(), U): pair[(x, y)].append(u)
    two = collections.Counter()
    for (x, y), us in pair.items():
        for i in range(len(us)):
            for j in range(i + 1, len(us)): two[cls(us[i] @ us[j].conj().T)] += 1
    # plaquettes: 4 cubes around a lattice edge, >= 2 owners, all 4 cubes in the patch
    grid = P.grid; plq = collections.Counter()
    linkmap = {}
    for x, y, kk, u in zip(a.tolist(), b.tolist(), k.tolist(), U): linkmap.setdefault((x, y, kk), u)
    for ax in range(3):
        b_, c_ = [q for q in range(3) if q != ax]; sh = np.array(grid.shape)
        for idx in np.argwhere(np.ones(tuple(sh - np.eye(3, dtype=int)[b_] - np.eye(3, dtype=int)[c_]), bool)):
            q0 = idx.copy(); cubes_ = []
            for dp in ((0, 0), (1, 0), (1, 1), (0, 1)):
                q = q0.copy(); q[b_] += dp[0]; q[c_] += dp[1]; cubes_.append(int(grid[tuple(q)]))
            if min(cubes_) < 0 or len(set(cubes_)) < 2: continue
            W = np.eye(2, dtype=complex); steps = (b_, c_, b_, c_)
            for s in range(4):
                o1, o2 = cubes_[s], cubes_[(s + 1) % 4]
                if o1 == o2: continue
                u = linkmap.get((o1, o2, steps[s]));
                if u is None: u = linkmap[(o2, o1, steps[s])].conj().T
                W = W @ u
            plq[cls(W)] += 1
    return {'two_cycles': dict(two), 'plaquettes': dict(plq)}

def cmd_balls(spec, R=8, nproc=4):
    dec = C.rule(spec); types_, n0, _ = C.legal_types(dec); keys = list(types_)
    balls, info = C.enumerate_balls(dec, R, max(1, math.ceil(math.log2(R))), types_, nproc)
    rho = Fraction(R) - C.RC_BOUND; d2s = set()
    for G, T, c in types_.values():
        P = C.Patch(G, T); a, b, _ = P.panels(); X = C.centroid14(G, T); d2s |= set(((X[a] - X[b]) ** 2).sum(1).tolist())
    tab = C.amp_table_exact(rho, d2s); rows = []
    for kb, (G, T, origin) in balls.items():
        Ha, Hp, _ = C.ball_amplified(G, T, rho, tab.__getitem__)
        lp = float(np.linalg.eigvalsh(Hp.toarray())[0]); la = float(np.linalg.eigvalsh(Ha.toarray())[0]); rows.append((lp, la, kb, origin))
    rows.sort(key=lambda r: r[0]); out = {'rule': str(spec), 'R': R, 'balls': len(rows), 'types': len(keys), 'D_float': rows[0][0],
                                          'Lambda_float': min(r[1] for r in rows), 'lowest_D': [], 'lowest_Lambda_balls_D': []}
    # the lowest balls: centre type, centre loops, ball holonomy, fingerprint
    for lp, la, kb, (ti, tidx) in rows[:5]:
        G, T, _ = balls[kb]; Gc, Tc, cc = types_[keys[ti]]; th2, th3 = Lc.centre_loops(Gc, Tc, cc)
        sk, fp, _ = fingerprint(G, T)
        out['lowest_D'].append({'D_ball': lp, 'Lambda_ball': la, 'centre_type_index': ti, 'centre_theta2': th2, 'centre_theta3': th3,
                                'shape': sk, 'fingerprint': fp, 'tiles': int(len(G)), **ball_holonomy(G, T)})
    byL = sorted(rows, key=lambda r: r[1])[:3]; out['lowest_Lambda_balls_D'] = [{'Lambda_ball': r[1], 'D_ball': r[0]} for r in byL]
    # all fingerprints, for cross-rule matching
    fps = collections.Counter(); shapes = collections.Counter()
    for lp, la, kb, origin in rows:
        G, T, _ = balls[kb]; sk, fp, _ = fingerprint(G, T); fps[(sk, fp)] += 1; shapes[sk] += 1
    out['n_shapes'] = len(shapes); out['fingerprints'] = sorted(f'{a}:{b}' for a, b in fps)
    out['D_by_fingerprint'] = {f'{fingerprint(balls[kb][0], balls[kb][1])[0]}:{fingerprint(balls[kb][0], balls[kb][1])[1]}': lp for lp, la, kb, o in rows[:40]}
    log({k: v for k, v in out.items() if k not in ('fingerprints', 'D_by_fingerprint')})
    save(str(spec), out)

if __name__ == '__main__':
    os.environ.setdefault('OMP_NUM_THREADS', '1')
    if sys.argv[1] == 'balls': cmd_balls(sys.argv[2], int(sys.argv[3]) if len(sys.argv) > 3 else 8, int(sys.argv[4]) if len(sys.argv) > 4 else 4)

def star_fingerprints(spec):
    """per legal 1-star type: (shape, Dirichlet-spectrum fingerprint), U0, U1, theta2"""
    dec = C.rule(spec); types_, _, _ = C.legal_types(dec); out = []
    for key, (G, T, c) in types_.items():
        Gt = G[c]; Grel = np.einsum('ji,njk->nik', Gt, G); Trel = (T - T[c]) @ Gt
        sk, fp, u0 = fingerprint(Grel, Trel); Gi, Ti = C.inflate(G, T, dec); u1 = float(np.linalg.eigvalsh(C.operators(Gi, Ti).toarray())[0])
        th2, th3 = Lc.centre_loops(G, T, c); out.append({'shape': sk, 'fp': fp, 'U0': u0, 'U1': u1, 'theta2': th2, 'theta3': th3})
    return out

def cmd_compare(a='4752', b='4753'):
    A, B = star_fingerprints(a), star_fingerprints(b)
    fa = {(r['shape'], r['fp']) for r in A}; fb = {(r['shape'], r['fp']) for r in B}
    amin = min(A, key=lambda r: r['U1']); flat = [r for r in A if r['theta2'] < 1e-9]
    res = {'rules': [a, b], 'types': [len(A), len(B)], 'shapes': [len({r['shape'] for r in A}), len({r['shape'] for r in B})],
           'shared_star_fingerprints': len(fa & fb), 'U1_argmin_of_a': {k: amin[k] for k in ('U0', 'U1', 'theta2', 'theta3')},
           'U1_argmin_of_a_present_in_b': (amin['shape'], amin['fp']) in fb,
           'U1_argmin_shape_present_in_b': amin['shape'] in {r['shape'] for r in B},
           'b_types_on_that_shape': sorted([{k: r[k] for k in ('U0', 'U1', 'theta2')} for r in B if r['shape'] == amin['shape']], key=lambda r: r['U1'])[:6],
           'a_twocycle_flat_types': [{k: r[k] for k in ('U0', 'U1', 'theta3')} for r in flat],
           'a_twocycle_flat_present_in_b': [(r['shape'], r['fp']) in fb for r in flat],
           'b_twocycle_flat_types': sum(r['theta2'] < 1e-9 for r in B),
           'U1_sorted_a': sorted(r['U1'] for r in A)[:6], 'U1_sorted_b': sorted(r['U1'] for r in B)[:6]}
    log(res); save(f'compare_{a}_{b}', res)

if __name__ == '__main__' and sys.argv[1] == 'compare': cmd_compare(*sys.argv[2:4])
