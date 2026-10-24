#!/usr/bin/env python3
"""Phase XI: radius-1 environment data of a Chair44 rule (independent recomputation, phase11_chair only).

For every Phi-closed legal 1-star type tau (complete set when the frame substitution is irreducible; Theorem XI.D):
  U0(tau)  = lambda_min of the pinned 1-star (24 - A on the star; >= E_*)
  U1(tau)  = lambda_min of the pinned sigma(tau) (>= E_*)
  mu0(tau) = lambda_min of the free 1-star
  theta2(tau) = the largest holonomy angle of a two-cycle based at the centre (0 if every two-cycle at the centre is trivial)
  theta3(tau) = the largest holonomy angle of a based triangle centre -> a -> b -> centre inside the star
Rule-level: U0, U1, mu0 (minima), argmin type keys, number of types with theta2 = 0, min over types of max(theta2, theta3),
the closed-form loop-transport bound (Theorem XI.F): if every centre has a non-trivial two-cycle,
  E_* >= 1 / max over panels of the transport load <= ... >= min_tau sin^2(theta2(tau)/2)   (two endpoints per panel, length 2),
and the frame-substitution graph.
Usage: python -u -I audit/phase11_local.py <set> [nproc]   sets: census | twins | counterfactual -> audit/results/phase11_local_<set>.jsonl"""
import os, sys, json, time, math, collections, types, hashlib
sys.modules.setdefault('resource', types.SimpleNamespace(getrusage=lambda *a: types.SimpleNamespace(ru_maxrss=0), RUSAGE_SELF=0))
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); RES = os.path.join(HERE, 'results')
import numpy as np, scipy.sparse.linalg as sla
import phase11_chair as C
T0 = time.time()
def log(*a): print(f"[{time.time()-T0:7.0f}s]", *a, flush=True)

def lmin(H):
    if H.shape[0] <= 700: return float(np.linalg.eigvalsh(H.toarray())[0])
    return float(sla.eigsh(H, k=1, which='SA', tol=1e-11, ncv=40, return_eigenvectors=False)[0])
def angle(W): return math.acos(max(-1.0, min(1.0, np.trace(W).real / 2)))

def centre_loops(G, T, c):
    """best two-cycle and triangle holonomy angles at the centre tile c of a 1-star patch"""
    P = C.Patch(G, T); a, b, k = P.panels(); U = C.link_matrices(G, a, b, k)
    out = collections.defaultdict(list)                 # x -> list of (y, U(x -> y))
    for x, y, u in zip(a.tolist(), b.tolist(), U):
        out[x].append((y, u)); out[y].append((x, u.conj().T))
    th2 = 0.0; th3 = 0.0
    nb = collections.defaultdict(list)
    for y, u in out[c]: nb[y].append(u)
    for y, us in nb.items():
        for i in range(len(us)):
            for j in range(len(us)):
                if i != j: th2 = max(th2, angle(us[i] @ us[j].conj().T))
    for y1, us1 in nb.items():
        for (y2, u12) in out[y1]:
            if y2 == c or y2 not in nb: continue
            for u1 in us1:
                for u2 in nb[y2]:
                    th3 = max(th3, angle(u1 @ u12 @ u2.conj().T))
    return th2, th3

def record(spec, per_type=True):
    t0 = time.time(); dec = C.rule(spec); types_, n0, phimap = C.legal_types(dec); rows = []
    keys = list(types_)
    for key in keys:
        G, T, c = types_[key]
        U0 = lmin(C.operators(G, T)); mu0 = lmin(C.operators(G, T, free=True))
        Gi, Ti = C.inflate(G, T, dec); U1 = lmin(C.operators(Gi, Ti)); th2, th3 = centre_loops(G, T, c)
        rows.append((U0, U1, mu0, th2, th3))
    R = np.array(rows); iU1 = int(R[:, 1].argmin()); iU0 = int(R[:, 0].argmin())
    th = np.maximum(R[:, 3], R[:, 4])
    rec = {'rule': str(spec), 'n_types1': len(keys), 'n_types1_T5': n0, 'U0': float(R[:, 0].min()), 'U1': float(R[:, 1].min()),
           'mu0': float(R[:, 2].min()), 'U1_sorted5': np.sort(R[:, 1])[:5].tolist(), 'U1_argmin_key': str(keys[iU1]), 'U0_argmin_key': str(keys[iU0]),
           'types_without_nontrivial_twocycle': int((R[:, 3] < 1e-9).sum()), 'types_without_short_loop': int((th < 1e-9).sum()),
           'min_theta2': float(R[:, 3].min()), 'min_theta_short': float(th.min()),
           'U1_of_twocycle_flat_types': sorted(R[R[:, 3] < 1e-9, 1].tolist())[:10],
           'twocycle_transport_bound': float(np.min(np.sin(R[:, 3] / 2) ** 2)) if (R[:, 3] > 1e-9).all() else 0.0,
           'frame_graph': C.frame_graph(dec), 'seconds': time.time() - t0}
    if per_type: rec['per_type'] = [{'key_hash': hashlib.sha1(str(k).encode()).hexdigest()[:12], 'U0': r[0], 'U1': r[1], 'mu0': r[2], 'theta2': r[3], 'theta3': r[4]} for k, r in zip(keys, rows)]
    return rec

def specs(which):
    pre = json.load(open(os.path.join(RES, 'phase11_preregistration.json')))
    if which == 'census':
        cen = json.load(open(os.path.join(RES, 'phase10_census.json')))['classes']; return [str(r['class']) for r in cen]
    if which == 'twins':
        import phase11_frontier as F
        S = C.perm_matrix((1, 0, 2)); out = []
        for r in pre['part_II_twin_criterion']['classes']:
            d = C.proper_decoration(r); tw = tuple(tuple(int(np.argmax((C.perm_matrix(p) @ S)[i])) for i in range(3)) for p in d)
            out += [str(r), 'x%d' % F.ext_index(tw)]
        return out
    if which == 'counterfactual':
        cf = pre['part_V_counterfactuals']; return ['4752', '4753'] + ['x%d' % j for j in cf['neighbours_FR30'] + cf['neighbours_4753']]
    raise ValueError(which)

if __name__ == '__main__':
    import multiprocessing as mp
    os.environ.setdefault('OMP_NUM_THREADS', '1')
    which = sys.argv[1]; nproc = int(sys.argv[2]) if len(sys.argv) > 2 else 4
    out = os.path.join(RES, f'phase11_local_{which}.jsonl'); done = set()
    if os.path.exists(out): done = {json.loads(l)['rule'] for l in open(out)}
    todo = [s for s in dict.fromkeys(specs(which)) if s not in done]; log(f'{which}: {len(todo)} rules to do')
    with mp.Pool(nproc) as pool, open(out, 'a') as f:
        import functools
        for i, rec in enumerate(pool.imap_unordered(functools.partial(record, per_type=(which != 'census')), todo)):
            f.write(json.dumps(rec) + '\n'); f.flush()
            if i % 50 == 0: log(f"{i + 1}/{len(todo)} {rec['rule']}: U1 {rec['U1']:.4f} types {rec['n_types1']} flat2 {rec['types_without_nontrivial_twocycle']}")
