#!/usr/bin/env python3
"""Phase VII (I.3, the protocol's "separate, labelled attempt"): do periodic chair tilings with all 1-stars legal exist?

If a periodic Y0 had all its 1-stars in V_1, then sigma^k(Y0) would be periodic with all 2^k-stars legal (closure lemma), i.e.
a genuine family of radius-R approximants, and Theorem I.4 would force their floors to E_FR30.  Exhaustive backtracking
(exact cover of the torus Z^3/L by chairs with proper frames, every 1-star required to lie in V_1, partial stars pruned by
"known part subset of some legal type") over period lattices L = m * Lambda for the two index-7 chair lattices
Lambda = ker(x + 2y + 4z mod 7), ker(x + 4y + 2z mod 7), and m = 1..M.
Positive controls: (i) with legality switched off the search finds the chair crystal; (ii) with the legal set replaced by the
1-star types of the V-A approximant P_1 (on 2 Lambda_7) it finds P_1; (iii) the torus code reproduces phase7_local's count of
illegal 1-stars of P_1 (7 of 8).
Usage: python -u -I audit/phase7_periodic_search.py [M] -> audit/results/phase7_periodic_search.json"""
import os, sys, json, time, itertools
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); RES = os.path.join(HERE, 'results')
import numpy as np
import phase7_local as P
T0 = time.time()
def log(*a): print(f"[{time.time()-T0:7.0f}s]", *a, flush=True)
LB = P.LB; ODD1 = P.LODD[1]
CHAIR_OFF = [tuple(int(x) for x in v) for v in itertools.product((0, 1), repeat=3) if v != (1, 1, 1)]

class Torus:
    def __init__(self, m, phi):
        self.m, self.phi = m, np.array(phi); self.n = 7 * m ** 3
    def cls(self, c):
        c = np.asarray(c); r = c % self.m; q = c // self.m
        return int(((r[0] * self.m + r[1]) * self.m + r[2]) * 7 + int(self.phi @ q) % 7)

def tile_cubes(gi, t): return [tuple(int(x) for x in c) for c in P.cubes_of_poses(P.Gs[gi][None], np.array(t)[None])[0]]

class Search:
    def __init__(self, tor, legal, limit_nodes=5_000_000, max_solutions=1):
        self.tor, self.legal, self.limit, self.maxsol = tor, legal, limit_nodes, max_solutions
        self.legal_list = None if legal is None else list(legal)
        self.owner = [-1] * tor.n; self.tiles = []; self.nodes = 0; self.solutions = []; self.progress = None
        # class order: raster order of representatives in a box, so the search fills space coherently
        reps = {}
        for c in itertools.product(range(7 * tor.m), range(tor.m), range(tor.m)):
            q = tor.cls(c)
            if q not in reps: reps[q] = c
        assert len(reps) == tor.n
        self.order = sorted(reps, key=lambda q: reps[q][::-1]); self.rep = reps
    def instance(self, c):
        """(tile index, translated pose) of the tile instance covering integer cube c, or None"""
        j = self.owner[self.tor.cls(c)]
        if j < 0: return None
        gi, t, cubes, cmap = self.tiles[j]; d = np.array(c) - np.array(cmap[self.tor.cls(c)])
        return j, gi, np.array(t) + d
    def star(self, j):
        gi, t, _, _ = self.tiles[j]; g = P.Gs[gi]; S = set(); complete = True
        for c in P.cubes_of_poses(g[None], np.array(t)[None], ODD1)[0]:
            inst = self.instance(tuple(int(x) for x in c))
            if inst is None: complete = False; continue
            _, gb, tb = inst; S.add(int(P.encode(P.MULT[P.INV[gi], gb], g.T @ (tb - np.array(t)))))
        return frozenset(S), complete
    def ok_tile(self, j):
        if self.legal is None: return True
        S, complete = self.star(j)
        if complete: return S in self.legal
        return any(S <= tau for tau in self.legal_list)
    def place(self, gi, t):
        cubes = tile_cubes(gi, t); cl = [self.tor.cls(c) for c in cubes]
        if len(set(cl)) < 7 or any(self.owner[q] >= 0 for q in cl): return None
        j = len(self.tiles); self.tiles.append((gi, tuple(t), cubes, dict(zip(cl, cubes))))
        for q in cl: self.owner[q] = j
        return j
    def remove(self):
        gi, t, cubes, cmap = self.tiles.pop()
        for q in cmap: self.owner[q] = -1
    def neighbours(self, j):
        gi, t, _, _ = self.tiles[j]; out = {j}
        for c in P.cubes_of_poses(P.Gs[gi][None], np.array(t)[None], ODD1)[0]:
            inst = self.instance(tuple(int(x) for x in c))
            if inst is not None: out.add(inst[0])
        return out
    def run(self):
        self._rec(0); return self
    def _rec(self, k):
        if len(self.solutions) >= self.maxsol or self.nodes >= self.limit: return
        while k < len(self.order) and self.owner[self.order[k]] >= 0: k += 1
        if k == len(self.order):
            if all(self.ok_tile(j) for j in range(len(self.tiles))): self.solutions.append([(int(g), list(t)) for g, t, _, _ in self.tiles])
            return
        c = np.array(self.rep[self.order[k]])
        for gi in range(P.NG):
            g = P.Gs[gi]
            for u in CHAIR_OFF:
                t = c + (1 - g @ (2 * np.array(u) + 1)) // 2
                j = self.place(gi, t)
                if j is None: continue
                self.nodes += 1
                if self.progress and self.nodes % 100000 == 0: log(f"   {self.progress}: {self.nodes} nodes, depth {len(self.tiles)}")
                if all(self.ok_tile(i) for i in self.neighbours(j)): self._rec(k + 1)
                self.remove()
                if len(self.solutions) >= self.maxsol or self.nodes >= self.limit: return

def legal_V1():
    G4, T4 = P.gen_poses(4); grid4 = P.owner_grid(4, G4, T4); cnt1, _ = P.star_types(G4, T4, grid4, P.LODD[1])
    seed = max(cnt1, key=cnt1.get); V1 = {seed}; fr = [seed]
    while fr:
        new = [kk for k in fr for kk in P.Phi_r(k, P.LODD[1]) if kk not in V1]
        for kk in new: V1.add(kk)
        fr = list(set(new))
    assert len(V1) == 72; return V1

def p1_on_torus():
    """the V-A approximant P_1 (level-1 FR30 supertile on 2 Lambda_7) as a filled Search state, and its 1-star types"""
    s = Search(Torus(2, (1, 2, 4)), None); G, T = P.gen_poses(1)
    for g, t in zip(G, T): assert s.place(P.gidx[P.key(g)], t) is not None
    assert all(q >= 0 for q in s.owner)
    return s, [s.star(j)[0] for j in range(len(s.tiles))]

if __name__ == '__main__':
    # usage: phase7_periodic_search.py M            (controls + all m <= M, both lattices, 20M-node cap)
    #        phase7_periodic_search.py one m a b c CAP  (one torus m*ker(ax+by+cz mod 7) with node cap CAP; appends to the JSON)
    path = os.path.join(RES, 'phase7_periodic_search.json')
    if sys.argv[1] == 'one':
        m, phi, cap = int(sys.argv[2]), tuple(int(x) for x in sys.argv[3:6]), int(sys.argv[6]); V1 = legal_V1()
        t0 = time.time(); s = Search(Torus(m, phi), V1, limit_nodes=cap); s.progress = f'm={m} phi={phi}'; s.run()
        row = {'lattice': f'{m} * ker(x*{phi[0]} + y*{phi[1]} + z*{phi[2]} mod 7)', 'tiles_per_period': m ** 3, 'nodes': s.nodes, 'node_cap': cap,
               'exhausted': s.nodes < s.limit and not s.solutions, 'solutions_found': len(s.solutions), 'seconds': time.time() - t0}
        log(row); out = json.load(open(path)); out['search'] = [r for r in out['search'] if r['lattice'] != row['lattice']] + [row]
        json.dump(out, open(path, 'w'), indent=1); sys.exit(0)
    M = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    V1 = legal_V1(); out = {'controls': {}, 'search': []}
    s1, types1 = p1_on_torus(); ill = sum(1 for k in types1 if k not in V1)
    out['controls']['P1_illegal_1stars'] = ill; log(f"control (iii): P_1 on the torus has {ill}/8 illegal 1-stars (phase7_local: 7/8)")
    s = Search(Torus(1, (1, 2, 4)), None).run(); out['controls']['crystal_found_without_legality'] = len(s.solutions) > 0
    log(f"control (i): legality off, m = 1: solution found {len(s.solutions) > 0} ({s.nodes} nodes)")
    s = Search(Torus(2, (1, 2, 4)), set(types1), max_solutions=1).run(); out['controls']['P1_found_with_P1_types'] = len(s.solutions) > 0
    log(f"control (ii): legal set = P_1's 1-star types, m = 2: solution found {len(s.solutions) > 0} ({s.nodes} nodes)")
    for phi in ((1, 2, 4), (1, 4, 2)):
        for m in range(1, M + 1):
            t0 = time.time(); s = Search(Torus(m, phi), V1, limit_nodes=20_000_000).run()
            row = {'lattice': f'{m} * ker(x*{phi[0]} + y*{phi[1]} + z*{phi[2]} mod 7)', 'tiles_per_period': m ** 3, 'nodes': s.nodes,
                   'exhausted': s.nodes < s.limit and not s.solutions, 'solutions_found': len(s.solutions), 'seconds': time.time() - t0}
            out['search'].append(row); log(row)
            json.dump(out, open(os.path.join(RES, 'phase7_periodic_search.json'), 'w'), indent=1)
    json.dump(out, open(os.path.join(RES, 'phase7_periodic_search.json'), 'w'), indent=1)
