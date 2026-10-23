#!/usr/bin/env python3
"""Phase VII (II.3, item D of the brief): certified radius-2 lower bounds L_2(rule) on inf spec(24 - A_U) for the 264 V-D rule
classes, with the machinery of audit/phase7_local.py re-parameterised by the decoration (V-B framework: legal 1-stars = forward
Phi-orbit of a seed found in T_4, legal 2-stars = Phi_2(V_1), validated by the census of complete 2-stars in T_5; 27-cube blocks,
weight 1/18; rigorous Higham certificates).  Compared with the Abelian reflection-only floor E_inf(Z2) <= 3.8222528 (certified).
Usage: python -u -I audit/phase7_decoration_bounds.py <shard> <nshards>   -> audit/results/phase7_decoration_bounds_shard<k>.jsonl"""
import os, sys, json, time
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); RES = os.path.join(HERE, 'results')
import numpy as np
import phase7_local as P
import phase5b_sweep as sw

def rule_bound(index):
    dec = sw.decoration(index); ops = P.make_ops(dec)
    P.OPS = ops; P.GOPS = np.array([g for g, t in ops]); P.TOPS = np.array([t for g, t in ops])
    t0 = time.time()
    G4, T4 = P.gen_poses(4); grid4 = P.owner_grid(4, G4, T4); cnt1, _ = P.star_types(G4, T4, grid4, P.LODD[1])
    seed = max(cnt1, key=cnt1.get); V = {1: {seed}}; frontier = [seed]
    while frontier:
        new = []
        for k in frontier:
            for kk in P.Phi_r(k, P.LODD[1]):
                if kk not in V[1]: V[1].add(kk); new.append(kk)
        frontier = new
    V[2] = {kk for k in V[1] for kk in P.Phi_r(k, P.LODD[2])}
    G5, T5 = P.gen_poses(5); grid5 = P.owner_grid(5, G5, T5)
    c1, _ = P.star_types(G5, T5, grid5, P.LODD[1]); c2, _ = P.star_types(G5, T5, grid5, P.LODD[2])
    res = P.block_bound(V, 2, exact_sample=10)
    return {'index': index, 'V1': len(V[1]), 'V2': len(V[2]), 'census_T5_subset_V1': set(c1) <= V[1], 'census_T5_subset_V2': set(c2) <= V[2],
            'census_T5_equal_V2': set(c2) == V[2], 'L2_certified': res['L_R_certified'], 'L2_value': res['L_R_float_value'],
            'L2_float': res['L_R_float_uncertified'], 'signatures': res['signatures'], 'seconds': time.time() - t0}

if __name__ == '__main__':
    shard, nsh = int(sys.argv[1]), int(sys.argv[2])
    rules = sorted(json.load(open(os.path.join(RES, 'phase5d_protocol.json')))['rule_indices'])
    path = os.path.join(RES, f'phase7_decoration_bounds_shard{shard}.jsonl'); done = set()
    if os.path.exists(path): done = {json.loads(l)['index'] for l in open(path)}
    with open(path, 'a') as f:
        for j, i in enumerate(rules):
            if j % nsh != shard or i in done: continue
            r = rule_bound(i); f.write(json.dumps(r) + '\n'); f.flush()
            print(f"rule {i}: V1 {r['V1']} V2 {r['V2']} census ok {r['census_T5_subset_V2']} L2 {r['L2_value']:.6f} ({r['seconds']:.0f}s)", flush=True)
