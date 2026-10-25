#!/usr/bin/env python3
"""Phase XII, Part VI: the support-sensitive transport (cycle-cover) bound, evaluated on Chair44 rules.

Theorem 6.1 (report section 6): for any family of simple cycles C with weights w_C >= 0, theta_C the least |argument| of an
eigenvalue of the holonomy of C and l_C its length, lambda_C = 2(1 - cos(theta_C / l_C)),
    E_* >= inf_v sum_{C ∋ v} w_C lambda_C / sup_e sum_{C ∋ e} w_C.
Applied with all cycles of a fixed local kind and w_C = 1, both sums are functions of the legal 1-star of v (support): the
infimum runs over the legal 1-star types only, and no localisation error enters.  Cycles used (all inside the 1-star of the
centre tile t, through t):
  two-cycles  t ->f b ->g t for two panels f, g between t and b with different normal axes (length 2)
  plaquettes  the lattice-edge 4-cycles through a cube of t with 3 or 4 distinct owners (simple cycles of length 3 or 4);
              those with 2 owners are two-cycles (counted above) or not simple (excluded)
Holonomies are exact Q8 quaternions (phase12_independent), so theta_C is 0 (W = 1), pi (W = -1) or pi/2 (traceless).
Usage: python -u -I audit/phase12_transport.py <rule> ... -> audit/results/phase12_transport.json (merged by rule)"""
import os, sys, json, math, itertools, collections
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); RES = os.path.join(HERE, 'results')
import phase12_independent as I
OUT = os.path.join(RES, 'phase12_transport.json')

def theta(q):
    return 0.0 if q == (1, 0, 0, 0) else math.pi if q == (-1, 0, 0, 0) else math.pi / 2
def inv(q): return (q[0], -q[1], -q[2], -q[3])
def cycles_of_star(fs, Ts, c):
    """cycles through the centre c of a legal 1-star patch: list of (lambda_C, [panel ids]) with panel ids (a, b, k, cube)"""
    O = I.Owner(fs, Ts); g = O.grid; out = []
    pan = collections.defaultdict(list); Qa = I.cubes(fs, Ts) - O.lo
    def own(q):
        q = np.asarray(q); return int(g[tuple(q)]) if ((q >= 0) & (q < np.array(g.shape))).all() else -1
    def link(a, b, k):                       # crossing from a to b along +e_k
        return I.Q8[I.LINK[fs[a], fs[b], k]]
    for q in map(tuple, Qa[c]):
        for k in range(3):
            for s in (1, -1):
                r = list(q); r[k] += s; b = own(r)
                if b >= 0 and b != c:
                    lo = q if s == 1 else tuple(r)
                    pan[b].append((k, lo, link(c, b, k) if s == 1 else inv(link(b, c, k))))
    for b, ps in pan.items():
        for (k1, lo1, u1), (k2, lo2, u2) in itertools.combinations(ps, 2):
            if k1 == k2: continue
            W = I.qmul(u1, inv(u2)); out.append((2 * (1 - math.cos(theta(W) / 2)), [('P', k1, lo1), ('P', k2, lo2)]))
    # plaquettes through a cube of c
    seen = set()
    for q in map(tuple, Qa[c]):
        for ax in range(3):
            b_, c_ = [x for x in range(3) if x != ax]
            for d1 in (0, -1):
                for d2 in (0, -1):
                    q0 = list(q); q0[b_] += d1; q0[c_] += d2; key = (ax, tuple(q0))
                    if key in seen: continue
                    seen.add(key); cyc = []
                    for dp in ((0, 0), (1, 0), (1, 1), (0, 1)):
                        r = list(q0); r[b_] += dp[0]; r[c_] += dp[1]; cyc.append((own(r), tuple(r)))
                    owners = [o for o, _ in cyc]
                    if min(owners) < 0: continue
                    red = [o for i, o in enumerate(owners) if o != owners[i - 1]]     # cyclic owner sequence, repeats merged
                    if len(red) < 3 or len(set(red)) != len(red): continue          # not a simple cycle of length >= 3
                    W = (1, 0, 0, 0); edges = []; steps = (b_, c_, b_, c_); sgn = (1, 1, -1, -1)
                    for s in range(4):
                        (o1, r1), (o2, r2) = cyc[s], cyc[(s + 1) % 4]
                        if o1 == o2: continue
                        k = steps[s]; lo = r1 if sgn[s] == 1 else r2
                        u = link(o1, o2, k) if sgn[s] == 1 else inv(link(o2, o1, k))
                        W = I.qmul(W, u); edges.append(('P', k, lo))
                    out.append((2 * (1 - math.cos(theta(W) / len(edges))), edges))
    return out

def bound(spec):
    types, n0 = I.legal_types(I.decoration(spec)); per_type = []; panel_load = collections.Counter(); W = 0
    for key, (fs, Ts, c) in types.items():
        cyc = cycles_of_star(fs, Ts, c); alpha = sum(l for l, _ in cyc)
        load = collections.Counter(e for _, es in cyc for e in es)          # cycles through c per panel of c
        per_type.append({'alpha': alpha, 'cycles': len(cyc), 'max_panel_load': max(load.values()) if load else 0,
                         'frustrated_cycles': sum(l > 0 for l, _ in cyc)})
    # W: the largest number of cycles of the family through one panel.  Every cycle through the panel f = {a, b} passes through
    # a, hence is in a's list: the load of f is counted exactly from either end, and W is the maximum over legal types.
    W = max(t['max_panel_load'] for t in per_type)
    beta = min(t['alpha'] for t in per_type) / W
    return {'rule': str(spec), 'types': len(types), 'W': W, 'alpha_min': min(t['alpha'] for t in per_type),
            'alpha_max': max(t['alpha'] for t in per_type), 'bound': beta,
            'types_without_frustrated_cycle': sum(t['frustrated_cycles'] == 0 for t in per_type)}

if __name__ == '__main__':
    d = json.load(open(OUT)) if os.path.exists(OUT) else {}
    for spec in sys.argv[1:]:
        r = bound(spec); d[str(spec)] = r; print(r, flush=True)
        json.dump(d, open(OUT, 'w'), indent=1)
