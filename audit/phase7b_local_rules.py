#!/usr/bin/env python3
"""Phase VII-B (C): do legal 1-stars force the FR30 hierarchy?  Finite checks that, together with the argument in
deliverables/PHASE7_REPORT.md section 6, prove  T_1 = Omega(FR30)  (every chair tiling with proper compatible frames whose 1-stars
are all legal FR30 1-stars is an element of the FR30 hull), hence aperiodicity of T_1 and E_inf(1) = E_FR30.

Objects (pose convention of phase7_local: a tile is (G, T), G one of the 24 proper rotations, cubes (G(2u+1) + 2T - 1)/2).
  V_1        legal 1-star types (forward Phi-orbit of a seed; completeness: section 6 of the report + primitivity checked here).
  role(tau)  (child index c, parent frame relative to the tile, parent translation relative to the tile at child scale),
             computed for EVERY (parent 1-star, child) pair from V_1 by inflation -- not from a census.
Checks.
  P   primitivity of the frame-decorated substitution (24 x 24 substitution matrix has a strictly positive power).
  R0  each legal 1-star type has exactly one role; every legal type arises as a child star (V_1 subset Phi(V_1)).
  S   for every legal 1-star, all 8 siblings predicted by its role are tiles of the star (same poses).
  A   sibling consistency: for every legal tau_a, every sibling b and every legal tau_b that is compatible with tau_a (equal
      cube ownership wherever both define it), role(tau_b) predicts the same parent as role(tau_a).
  B   desubstitution: enumerate every locally consistent configuration around a parent P (legal stars of its 8 children with
      the right roles, mutually compatible; then every neighbouring tile's parent, branching over compatible legal stars when
      it is not forced); the parent-level 1-star of P must be legal in every branch.
Usage: python -u -I audit/phase7b_local_rules.py [--per-star] -> audit/results/phase7b_local_rules.json"""
import os, sys, json, time, collections, itertools
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); RES = os.path.join(HERE, 'results')
import numpy as np
import phase7_local as P
T0 = time.time()
def log(*a): print(f"[{time.time()-T0:7.0f}s]", *a, flush=True)
ODD1 = P.LODD[1]; LB = P.LB

def legal_V1():
    G4, T4 = P.gen_poses(4); grid4 = P.owner_grid(4, G4, T4); cnt1, _ = P.star_types(G4, T4, grid4, ODD1)
    seed = max(cnt1, key=cnt1.get); V1 = {seed}; fr = [seed]
    while fr:
        new = {kk for k in fr for kk in P.Phi_r(k, ODD1) if kk not in V1}; V1 |= new; fr = list(new)
    return V1, seed

def primitivity():
    """M[f, f'] = number of children with frame f' of a tile with frame f; smallest n with M^n > 0."""
    M = np.zeros((P.NG, P.NG), np.int64)
    for f in range(P.NG):
        for g, t in P.OPS: M[f, P.gidx[P.key(P.Gs[f] @ g)]] += 1
    Mn = np.eye(P.NG, dtype=np.int64)
    for n in range(1, 30):
        Mn = np.minimum(Mn @ M, 10 ** 6)
        if (Mn > 0).all(): return n
    return None

# ------------------------------------------------------------------ stars as placeable objects
class Star:
    def __init__(self, k):
        poses, c = P.poses_from_key(k); assert c is not None
        self.k = k; self.rel = [(P.gidx[P.key(g)], np.asarray(t, np.int64)) for g, t in poses]
        self.c2 = [P.Gs[gi] @ (LB.T) + 2 * t[:, None] for gi, t in self.rel]        # doubled cube centres (3 x 7) per tile, star frame
    def place(self, gi, T):
        """dict cube -> pose (frame index, T tuple) of all tiles of the star placed at pose (Gs[gi], T)"""
        G = P.Gs[gi]; out = {}
        for (ri, t), c2 in zip(self.rel, self.c2):
            pose = (int(P.MULT[gi, ri]), tuple(int(x) for x in T + G @ t)); cubes = (G @ c2 + 2 * np.asarray(T)[:, None] - 1) // 2
            for q in cubes.T: out[tuple(int(x) for x in q)] = pose
        return out

def compatible(K, S):
    small, big = (S, K) if len(S) < len(K) else (K, S)
    return all(big.get(q, v) == v for q, v in small.items())

def parent_of(gi, T, role):
    """parent pose (frame index, P2 = 2 T_parent at child scale) of a tile with pose (gi, T) and role (c, prel, ptr)"""
    c, prel, ptr = role; G = P.Gs[gi]; P2 = np.asarray(T) + G @ np.asarray(ptr)
    return (int(P.MULT[gi, prel]), tuple(int(x) for x in P2))

def children_of(parent):
    gp, P2 = parent; Gp = P.Gs[gp]
    return [(int(P.gidx[P.key(Gp @ g)]), tuple(int(x) for x in np.asarray(P2) + Gp @ t)) for g, t in P.OPS]

def main():
    out = {}
    V1, seed = legal_V1(); V1l = sorted(V1, key=lambda z: sorted(z)); log(f"|V_1| = {len(V1)}")
    out['V1'] = len(V1); out['primitivity_power'] = primitivity(); log(f"P: substitution matrix on frames: M^n > 0 for n = {out['primitivity_power']}")
    # ---- R0: roles from inflation of every legal parent 1-star
    ROLES = collections.defaultdict(set); child_types = set()
    for kP in V1l:
        poses, cP = P.poses_from_key(kP); fine = P.inflate(poses); own = P.owner_dict(fine)
        for c in range(8):
            ga, ta = fine[8 * cP + c]; kk = P.star_key_in_patch(fine, own, 8 * cP + c, ODD1); assert kk is not None, 'closure lemma'
            ROLES[kk].add((c, int(P.gidx[P.key(ga.T)]), tuple(int(x) for x in ga.T @ (-np.asarray(ta)))))
            child_types.add(kk)
    out['R0'] = {'types_with_roles': len(ROLES), 'V1_subset_PhiV1': child_types == V1, 'max_roles_per_type': max(len(v) for v in ROLES.values()),
                 'role_counts_by_child_index': dict(collections.Counter(next(iter(v))[0] for v in ROLES.values()))}
    assert child_types == V1 and all(len(v) == 1 for v in ROLES.values())
    ROLE = {k: next(iter(v)) for k, v in ROLES.items()}; log(f"R0: {out['R0']}")
    STAR = {k: Star(k) for k in V1l}
    # ---- S: which siblings lie inside the 1-star (Chebyshev cube distance between children of a supertile)
    G1, T1 = P.gen_poses(1); C1 = P.cubes_of_poses(G1, T1)
    DCH = [[min(int(np.abs(x - y).max()) for x in C1[i] for y in C1[j]) for j in range(8)] for i in range(8)]
    out['child_distance_matrix'] = DCH; assert all(DCH[0][j] <= 1 for j in range(8))
    S_ok = True; S_far_missing = 0
    for k in V1l:
        c = ROLE[k][0]; par = parent_of(0, (0, 0, 0), ROLE[k]); poses = {(int(gi), tuple(int(x) for x in t)) for gi, t in STAR[k].rel}
        for j, ch in enumerate(children_of(par)):
            if DCH[c][j] <= 1: S_ok &= ch in poses
            else: S_far_missing += ch not in poses
    out['S'] = {'distance1_siblings_inside_every_1star': S_ok, 'centre_child_star_contains_all_8': S_ok,
                'distance2_siblings_missing_occurrences': S_far_missing}
    log(f"S: {out['S']}"); assert S_ok
    # ---- A: consistency for every sibling inside the star
    nA = 0; candA = []
    for k in V1l:
        Ka = STAR[k].place(0, np.zeros(3, np.int64)); par = parent_of(0, (0, 0, 0), ROLE[k]); c = ROLE[k][0]
        for j, (gb, Tb) in enumerate(children_of(par)):
            if j == c or DCH[c][j] > 1: continue
            nc = 0
            for kb in V1l:
                if compatible(Ka, STAR[kb].place(gb, np.array(Tb))):
                    nc += 1; nA += 1
                    assert parent_of(gb, Tb, ROLE[kb]) == par, 'sibling consistency fails'
            candA.append(nc); assert nc >= 1
    out['A'] = {'compatible_sibling_stars_checked': nA, 'candidates_per_sibling_max': max(candA), 'candidates_per_sibling_min': min(candA), 'ok': True}
    log(f"A: {out['A']}")
    # ---- B: desubstitution legality
    Pp = (0, (0, 0, 0)); kids = children_of(Pp)
    want = {c: (c, int(P.gidx[P.key(P.Gs[kids[c][0]].T)]), tuple(int(x) for x in P.Gs[kids[c][0]].T @ (-np.array(kids[c][1])))) for c in range(8)}
    bycls = collections.defaultdict(list)
    for k in V1l: bycls[ROLE[k]].append(k)
    pcubes = [tuple(int(x) for x in q) for q in P.cubes_of_poses(P.Gs[0][None], np.zeros((1, 3), np.int64), ODD1)[0]]   # parent-level 1-star region
    stats = collections.Counter(); bad = []; parent_stars = collections.Counter()
    def tiles_of(K):
        inv = collections.defaultdict(list)
        for q, pose in K.items(): inv[pose].append(q)
        return inv
    def finish(K, known):
        """known: dict tile pose -> parent pose; returns parent 1-star key of Pp (or raises)"""
        stars = set(); ownp = {}
        for qp in pcubes:
            par = None
            for d in itertools.product((0, 1), repeat=3):
                q = (2 * qp[0] + d[0], 2 * qp[1] + d[1], 2 * qp[2] + d[2]); pose = K.get(q)
                if pose is not None and pose in known: par = known[pose]; break
            assert par is not None, 'parent block not reached'
            # consistency: the parent's cubes contain qp
            P2 = np.array(par[1]); assert (P2 % 2 == 0).all(), 'parent off the aligned grid'
            pc = {tuple(int(x) for x in c) for c in P.cubes_of_poses(P.Gs[par[0]][None], (P2 // 2)[None])[0]}
            assert qp in pc; stars.add(par)
        return frozenset(int(P.encode(P.MULT[P.INV[Pp[0]], gq], P.Gs[Pp[0]].T @ ((np.array(tq) - np.array(Pp[1])) // 2))) for gq, tq in stars)
    PLACE = {}
    def placed(kb, pose):
        key_ = (kb, pose)
        if key_ not in PLACE: PLACE[key_] = STAR[kb].place(pose[0], np.array(pose[1]))
        return PLACE[key_]
    def need_poses(K):
        need = set()
        for qp in pcubes:
            for d in itertools.product((0, 1), repeat=3):
                pose = K.get((2 * qp[0] + d[0], 2 * qp[1] + d[1], 2 * qp[2] + d[2]))
                if pose is not None: need.add(pose)
        return need
    def rec_neigh(K, known, depth):
        """only tiles owning a child cube of a parent-level cube in P's 1-star region matter; for each, the legal stars
        compatible with everything known so far; forced parents are recorded, otherwise branch on the most constrained tile"""
        stats['nodes'] += 1
        if stats['nodes'] % 200 == 0: log(f"   B: {stats['nodes']} nodes, {stats['configurations']} configurations, {len(PLACE)} cached placements")
        best = None
        for pose in sorted(need_poses(K) - set(known)):
            cands = [kb for kb in V1l if compatible(K, placed(kb, pose))]
            preds = {parent_of(pose[0], pose[1], ROLE[kb]) for kb in cands}
            if not preds: stats['pruned_inconsistent'] += 1; return
            if len(preds) == 1: known[pose] = next(iter(preds))
            elif best is None or len(cands) < len(best[1]): best = (pose, cands)
        if best is None:
            key = finish(K, known); parent_stars[key] += 1; stats['configurations'] += 1
            if key not in V1: bad.append(sorted(key)); stats['illegal_parent_stars'] += 1
            return
        stats['branch_points'] += 1; pose, cands = best
        for kb in cands:
            K2 = dict(K); K2.update(placed(kb, pose)); kn = dict(known); kn[pose] = parent_of(pose[0], pose[1], ROLE[kb]); rec_neigh(K2, kn, depth + 1)
    def common(dicts):
        base = dicts[0]; return {q: v for q, v in base.items() if all(d.get(q) == v for d in dicts[1:])}
    def rec_grouped(K, known):
        """sound over-approximation: branch over the distinct predicted parents of the most ambiguous tile; each branch adds
        only the cube assignments common to every legal star in its group (the true star is in exactly one group)."""
        stats['nodes'] += 1
        if stats['nodes'] % 200 == 0: log(f"   B(grouped): {stats['nodes']} nodes, {stats['configurations']} configurations")
        changed = True
        while changed:
            changed = False; best = None
            for pose in sorted(need_poses(K) - set(known)):
                groups = collections.defaultdict(list)
                for kb in V1l:
                    S = placed(kb, pose)
                    if compatible(K, S): groups[parent_of(pose[0], pose[1], ROLE[kb])].append(S)
                if not groups: stats['pruned_inconsistent'] += 1; return
                if len(groups) == 1:
                    par, Ss = next(iter(groups.items())); known[pose] = par; cm = common(Ss)
                    if any(q not in K for q in cm): K = dict(K); K.update(cm)
                    changed = True
                elif best is None or len(groups) < len(best[1]): best = (pose, groups)
        if best is None:
            key = finish(K, known); parent_stars[key] += 1; stats['configurations'] += 1
            if key not in V1: bad.append(sorted(key)); stats['illegal_parent_stars'] += 1
            return
        stats['branch_points'] += 1; pose, groups = best
        for par, Ss in groups.items():
            K2 = dict(K); K2.update(common(Ss)); kn = dict(known); kn[pose] = par; rec_grouped(K2, kn)
    def rec_kids(c, K):
        if c == 8:
            known = {kids[i]: Pp for i in range(8)}
            (rec_grouped if GROUPED else rec_neigh)(K, known, *(() if GROUPED else (0,))); return
        for k in bycls[want[c]]:
            S = STAR[k].place(kids[c][0], np.array(kids[c][1]))
            if compatible(K, S):
                K2 = dict(K); K2.update(S); rec_kids(c + 1, K2)
    rec_kids(0, {}); log(f'B: done, {dict(stats)}')
    out['B'] = {**dict(stats), 'distinct_parent_1stars': len(parent_stars), 'parent_1stars_subset_V1': all(k in V1 for k in parent_stars),
                'parent_1stars_equal_V1': set(parent_stars) == V1, 'illegal_examples': bad[:3]}
    log(f"B: {out['B']}")
    out['B']['mode'] = 'grouped' if GROUPED else 'per-star'
    json.dump(out, open(os.path.join(RES, 'phase7b_local_rules' + ('' if GROUPED else '_perstar') + '.json'), 'w'), indent=1)

GROUPED = '--per-star' not in sys.argv          # default: grouped (sound over-approximation, fast); --per-star: exact enumeration (slow)
if __name__ == '__main__': main()
