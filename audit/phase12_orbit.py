#!/usr/bin/env python3
"""Phase XII, Part II: the right action of the chair's point group on frame rules, d -> d.Q (every child frame factor h_c
replaced by h_c Q, Q a permutation matrix).

  lemma     exact checks of the Orbit Lemma (deliverables/PHASE12_REPORT.md section 2):
              (a) sigma_{dQ} = rho_Q o sigma_d on poses, rho_Q(M, T) = (MQ, T), and rho_Q preserves every tile's cube set;
              (b) rho_Q is a global gauge transformation: for every pair of signed basis vectors (u_a, u_b),
                  (sigma . Q^T u_a)(sigma . Q^T u_b) = W_Q (sigma . u_a)(sigma . u_b) W_Q^+ with one fixed W_Q in SU(2);
              (c) hence the level-1 supertiles of d and dQ have unitarily equivalent pinned operators, and the three Abelian
                  shadows are permuted: checked for all 280 332 S3-conjugation representatives (Y1 and the full level-1 spectrum);
              (d) certified failure at level 2 for the orbit of 1387: disjoint enclosures of lambda_min(T_2);
              (e) failure in infinite volume: the stored certificates separate E_*(1387) from E_*(539288)
  funnel    the right-orbit structure of the certified funnel (all 280 332 representatives, exact Y3 of stage X3):
            share of the variance of Y3 explained by right orbits, rank correlation of Y3(d) with Y3(dQ), survival of whole orbits
  profile   the six members of the orbit of 1387 side by side (report section 2.3-2.4): pinned bottoms Y1..Y3, plaquette-class
            counts at levels 1-3, the number of legal 1-star types, and the bottoms of the three Abelian shadows on T3
            (python -u -I audit/phase12_orbit.py profile -> key 'profile', merged)
Usage: python -u -I audit/phase12_orbit.py -> audit/results/phase12_orbit.json  (uses phase12_independent for operators)"""
import os, sys, json, gzip, math, itertools, time
from fractions import Fraction
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); RES = os.path.join(HERE, 'results')
import phase12_independent as I
N8 = 6 ** 8
def JL(n):
    p = os.path.join(RES, n)
    if os.path.exists(p): return [json.loads(l) for l in open(p)]
    return [json.loads(l) for l in gzip.open(p + '.gz', 'rt')]
PIDX = {p: i for i, p in enumerate(I.PERM3)}
PM = [I.pmat(p) for p in I.PERM3]
def perm_of(M): return tuple(int(np.argmax(np.abs(M[i]))) for i in range(3))
RIGHT = np.array([[PIDX[perm_of(PM[p] @ PM[q])] for q in range(6)] for p in range(6)])        # P(p) P(q)
CONJ = np.array([[PIDX[perm_of(PM[q] @ PM[p] @ PM[q].T)] for p in range(6)] for q in range(6)])   # Q P Q^T
OCTMAP = np.array([[I.OCTANTS.index(tuple(int(x) for x in PM[q] @ np.array(v))) for v in I.OCTANTS] for q in range(6)])
def digits(j): return np.stack([(np.asarray(j) // 6 ** c) % 6 for c in range(8)], -1)
def index(D): return (D * (6 ** np.arange(8))).sum(-1)
def conj_index(D, q):
    out = np.empty_like(D); out[..., 0] = CONJ[q][D[..., 0]]
    for k in range(7): out[..., 1 + OCTMAP[q][k]] = CONJ[q][D[..., 1 + k]]
    return index(out)
def rep(D): return np.min(np.stack([conj_index(D, q) for q in range(6)], -1), -1)
def right(D, q): return RIGHT[D, q]
def ext_index_of(spec): return int(index(np.array([PIDX[p] for p in I.decoration(spec)])))

# ---------------------------------------------------------------- the lemma
def lemma():
    out = {}
    rng = np.random.default_rng(12)
    # (a) pose identity on random decorations and random parent poses, and cube-set invariance of rho_Q
    ok_pose, ok_cubes = True, True
    for _ in range(200):
        d = [I.PERM3[i] for i in rng.integers(0, 6, 8)]; q = int(rng.integers(0, 6)); dq = [I.PERM3[RIGHT[PIDX[p], q]] for p in d]
        f = rng.integers(0, 48, 5); T = rng.integers(-5, 5, (5, 3))
        fa, Ta = I.inflate(f, T, dq); fb, Tb = I.inflate(f, T, d)
        ok_pose &= np.array_equal(Ta, Tb) and np.array_equal(fa, I.FMUL[fb, I.fidx(PM[q])])
        ok_cubes &= np.array_equal(np.sort(I.cubes(fb, Tb).reshape(len(fb), -1), 1), np.sort(I.cubes(I.FMUL[fb, I.fidx(PM[q])], Tb).reshape(len(fb), -1), 1))
    out['a_pose_identity'] = bool(ok_pose); out['a_rhoQ_preserves_cubes'] = bool(ok_cubes)
    # (b) the link identity: find W_Q from two generic link values, then check all 48 x 48 x 3
    sig = np.array([[[0, 1], [1, 0]], [[0, -1j], [1j, 0]], [[1, 0], [0, -1]]])
    def sdot(u): return np.tensordot(u, sig, 1)
    def link(Ma, Mb, k): return sdot(Ma[k]) @ sdot(Mb[k])
    Wq = {}
    for q in range(6):
        Q = PM[q]; R = Q.T * round(np.linalg.det(Q.T))                     # the proper rotation det(Q^T) Q^T
        # its spin lift: W sigma.e W^+ = sigma.(R e) for e in the basis, solved as a linear null space
        A = np.vstack([np.kron(sdot(R @ e), np.eye(2)) - np.kron(np.eye(2), sdot(e).T) for e in np.eye(3)])
        _, s, Vh = np.linalg.svd(A); W = Vh[-1].conj().reshape(2, 2); W = W / np.sqrt(np.linalg.det(W))
        assert all(np.allclose(W @ sdot(e) @ W.conj().T, sdot(R @ e)) for e in np.eye(3))
        err = 0.0
        for i in range(48):
            for j in range(48):
                for k in range(3):
                    Ma, Mb = I.FRAMES[i], I.FRAMES[j]
                    err = max(err, float(np.abs(link(Ma @ Q, Mb @ Q, k) - W @ link(Ma, Mb, k) @ W.conj().T).max()))
        Wq[q] = W; out.setdefault('b_link_identity_max_error', 0.0); out['b_link_identity_max_error'] = max(out['b_link_identity_max_error'], err)
    # (b') the same identity in exact integer arithmetic: W_Q = x/|x| with x an integer quaternion (a Hurwitz unit times
    # 2 for the 3-cycles, (1 + q_l) or (q_l + q_m) up to scale for the transpositions), so  x u xbar = |x|^2 u'  exactly
    cand = [x for x in itertools.product(range(-1, 2), repeat=4) if any(x)]
    exact = {}
    for q in range(6):
        Qf = I.fidx(PM[q]); found = None
        for x in cand:
            n2 = sum(c * c for c in x); xb = (x[0], -x[1], -x[2], -x[3]); ok = True
            for i in range(48):
                for j in range(48):
                    for k in range(3):
                        u = I.Q8[I.LINK[i, j, k]]; up = I.Q8[I.LINK[I.FMUL[i, Qf], I.FMUL[j, Qf], k]]
                        if I.qmul(I.qmul(x, u), xb) != tuple(n2 * c for c in up): ok = False; break
                    if not ok: break
                if not ok: break
            if ok: found = list(x); break
        exact[str(I.PERM3[q])] = found
    out['b_exact_integer_quaternion_x'] = exact; out['b_exact_identity_holds'] = all(v is not None for v in exact.values())
    # (c) level-1: Y1 and the full level-1 spectrum constant on right orbits, all representatives; shadows permuted
    reps = np.array(json.load(open(os.path.join(RES, 'phase11_frontier_reps.json')))['orbit_representatives'])
    t0 = time.time(); f1, T1 = I.supertile(I.decoration('x0'), 1); O = I.Owner(f1, T1); P = O.panels()
    a, b, k = P[:, 0], P[:, 1], P[:, 2]
    FRC = np.array([[I.fidx((PM[0] if c == 0 else np.diag([1 - 2 * x for x in I.OCTANTS[c - 1]])) @ PM[p]) for p in range(6)] for c in range(8)])
    LQ = np.array(I._LQ, dtype=float)
    def level1_spec(D):
        """spectra of the pinned level-1 operators (spinor, realified) for decorations D (n, 8): child c of the root has frame h_c"""
        out = []
        for s0 in range(0, len(D), 20000):
            Dc = D[s0:s0 + 20000]; n = len(Dc); fr = FRC[np.arange(8)[None, :], Dc]
            H = np.zeros((n, 32, 32)); li = I.LINK[fr[:, a], fr[:, b], k[None, :]]
            for e in range(len(a)):
                L = LQ[li[:, e]]
                H[:, 4 * a[e]:4 * a[e] + 4, 4 * b[e]:4 * b[e] + 4] -= L; H[:, 4 * b[e]:4 * b[e] + 4, 4 * a[e]:4 * a[e] + 4] -= np.transpose(L, (0, 2, 1))
            out.append(np.linalg.eigvalsh(H + 24 * np.eye(32)))
        return np.concatenate(out)
    D = digits(reps); worst = 0.0
    S0 = level1_spec(D)
    for q in range(1, 6):
        Sq = level1_spec(right(D, q)); worst = max(worst, float(np.abs(Sq - S0).max()))
    out['c_level1_spectrum_constant_on_right_orbits_max_dev'] = worst; out['c_representatives_checked'] = int(len(reps)); out['c_seconds'] = time.time() - t0
    # (d) level 2 for the orbit of 1387: certified enclosures of lambda_min(T_2)
    d0 = np.array([PIDX[p] for p in I.decoration('4753')]); encl = {}
    for q in range(6):
        dq = [I.PERM3[x] for x in right(d0, q)]; f, T = I.supertile(dq, 2); H = I.operator(f, T)
        w, V = np.linalg.eigh(H.toarray()); up = I.exact_rayleigh(H, V[:, 0])
        lo, _ = I.higham(H, float(Fraction(math.floor(Fraction(w[0] - 1e-7) * 2 ** 30), 2 ** 30)), 0.0)
        encl[int(index(right(d0, q)))] = [lo, float(up)]
    iv = sorted(encl.values()); out['d_level2_enclosures'] = {str(k): v for k, v in encl.items()}
    out['d_level2_pairwise_disjoint'] = all(iv[i][1] < iv[i + 1][0] for i in range(len(iv) - 1))
    # (e) infinite volume from the stored certificates
    cert = {r['tag']: r for r in JL('phase11_cert.jsonl') if r.get('tag')}; y6 = {r['j']: r for r in JL('phase11_orbit_Y6.jsonl')}
    L1387 = Fraction(cert['target_1387_R20']['Lambda_R_certified']); U539288 = Fraction(int(y6[539288]['upper_num']), int(y6[539288]['upper_den']))
    out['e_E1387_lower'] = float(L1387); out['e_E539288_upper'] = float(U539288); out['e_separated'] = L1387 > U539288
    out['e_539288_is_1387_times_Q'] = [I.PERM3[q] for q in range(6) if int(rep(right(d0, q)[None])[0]) == 539288]
    return out

# ---------------------------------------------------------------- the funnel
def funnel():
    from scipy import stats
    reps = np.array(json.load(open(os.path.join(RES, 'phase11_frontier_reps.json')))['orbit_representatives'])
    X3 = {r['j']: r['float'] for r in JL('phase11_frontier_X3.jsonl')}; y = np.array([X3[j] for j in reps])
    pos = {int(j): i for i, j in enumerate(reps)}; D = digits(reps)
    R = np.stack([rep(right(D, q)) for q in range(6)], 1)                    # right-orbit members as representatives
    idx = np.vectorize(pos.get)(R)
    uniq = {tuple(sorted(set(row.tolist()))) for row in idx}
    def r2_of(v):
        m = np.zeros(len(v))
        for g in uniq: g = list(g); m[g] = v[g].mean()
        return 1 - ((v - m) ** 2).sum() / ((v - v.mean()) ** 2).sum()
    sizes = [len(g) for g in uniq]
    r2 = r2_of(y)
    rho = {str(I.PERM3[q]): float(stats.spearmanr(y, y[idx[:, q]]).statistic) for q in range(1, 6)}
    rng = np.random.default_rng(0); perm = rng.permutation(len(y))
    L = 8.7999987; surv3 = y >= L
    full = sum(1 for g in uniq if all(surv3[list(g)])); some = sum(1 for g in uniq if any(surv3[list(g)]))
    X4 = {r['j']: r for r in JL('phase11_frontier_X4.jsonl')}; s4 = {j for j, r in X4.items() if not r['inferior']}
    some4 = [g for g in uniq if any(int(reps[i]) in s4 for i in g)]
    return {'representatives': int(len(y)), 'right_orbits': len(uniq), 'orbit_size_histogram': {str(s): sizes.count(s) for s in sorted(set(sizes))},
            'Y3_variance_explained_by_right_orbits': float(r2), 'Y3_variance_explained_random_partition_same_sizes': float(r2_of(y[perm])),
            'spearman_Y3_d_vs_dQ': rho, 'X3_survivors': int(surv3.sum()), 'orbits_with_a_survivor_X3': some,
            'orbits_entirely_surviving_X3': full, 'X4_survivors': len(s4), 'orbits_with_an_X4_survivor': len(some4),
            'X4_survivor_orbits': [sorted(int(reps[i]) for i in g) for g in some4]}

# ---------------------------------------------------------------- the conjugation-defect law (preregistered)
def defect_law():
    """phase12_preregistration_delta.json: delta_Q(d) against |Y3(dQ) - Y3(d)| over all representatives and Q != id"""
    from scipy import stats
    reps = np.array(json.load(open(os.path.join(RES, 'phase11_frontier_reps.json')))['orbit_representatives'])
    X3 = {r['j']: r['float'] for r in JL('phase11_frontier_X3.jsonl')}; D = digits(reps); y = np.array([X3[j] for j in reps])
    dl, dy = [], []
    for q in range(1, 6):
        delta = (digits(np.stack([conj_index(D, q)], 0)[0]) != D).sum(1)
        yq = np.array([X3[int(j)] for j in rep(right(D, q))])
        dl.append(delta); dy.append(np.abs(yq - y))
    dl = np.concatenate(dl); dy = np.concatenate(dy)
    h0 = float(dy[dl == 0].max()) if (dl == 0).any() else None
    m = dl >= 1; rho = float(stats.spearmanr(dl[m], dy[m]).statistic)
    med = {int(k): float(np.median(dy[dl == k])) for k in range(9) if (dl == k).sum() >= 100}
    cnt = {int(k): int((dl == k).sum()) for k in range(9)}
    ks = sorted(med); mono = all(med[ks[i]] <= med[ks[i + 1]] for i in range(len(ks) - 1) if ks[i] >= 1)
    return {'pairs': int(len(dl)), 'pairs_by_delta': cnt, 'H0_max_abs_dY3_at_delta0': h0, 'H0_pass': h0 is None or h0 < 1e-9,
            'H1_spearman_delta_vs_abs_dY3': rho, 'H1_pass': rho >= 0.3, 'H2_median_abs_dY3_by_delta': med, 'H2_pass': mono,
            'mean_abs_dY3_by_delta': {int(k): float(dy[dl == k].mean()) for k in range(9) if (dl == k).any()}}

# ---------------------------------------------------------------- the closure of the lemma's moves
def closure():
    """the equivalence generated on decorations by (i) S3 conjugation (exact) and (ii) right multiplication by an element of the
    conjugation stabiliser of the current decoration (Orbit Lemma (d)); exhaustive comparison with exact Y3 ties inside right orbits:
    every pair in one class must tie (theorem), and every tie should be explained (the question: is there another mechanism?)"""
    reps = np.array(json.load(open(os.path.join(RES, 'phase11_frontier_reps.json')))['orbit_representatives'])
    X3 = {r['j']: r['float'] for r in JL('phase11_frontier_X3.jsonl')}; D = digits(reps)
    def cls(d0):
        seen = {tuple(d0)}; todo = [np.array(d0)]
        while todo:
            e = todo.pop(); E = e[None]
            nxt = [digits(conj_index(E, q))[0] for q in range(6)]
            nxt += [right(e, q) for q in range(6) if int(conj_index(E, q)[0]) == int(index(e))]
            for x in nxt:
                t = tuple(int(v) for v in x)
                if t not in seen: seen.add(t); todo.append(np.array(t))
        return {int(v) for v in rep(np.array(sorted(seen)))}
    ties_unexplained, explained_not_tied, pairs, ties = [], [], 0, 0
    for i, j in enumerate(reps):
        C = cls(D[i]); yj = X3[int(j)]
        for q in range(1, 6):
            k = int(rep(right(D[i], q)[None])[0]); pairs += 1; tie = abs(X3[k] - yj) < 1e-9; ties += tie
            if tie and k not in C: ties_unexplained.append((int(j), k, q))
            if (k in C) and not tie: explained_not_tied.append((int(j), k, q, X3[k] - yj))
    return {'pairs': pairs, 'ties': ties, 'ties_unexplained': len(ties_unexplained), 'examples_unexplained': ties_unexplained[:10],
            'explained_but_not_tied': len(explained_not_tied), 'examples_explained_not_tied': explained_not_tied[:10]}

# ---------------------------------------------------------------- the orbit of 1387, member by member
ORBIT_1387 = [('1387', '1387'), ('1389', '1389'), ('1391', '1391'), ('539311', 'x539311'), ('539291', 'x539291'), ('539288', 'x539288')]
def orbit_profile():
    import phase9_pair as P9, phase10_shadows as SH, phase11_chair as C
    lmin = lambda H: float(np.linalg.eigvalsh(H.toarray())[0])
    out = {}
    for name, spec in ORBIT_1387:
        d = C.rule(spec); dec = {'0': d[0], **{v: d[k + 1] for k, v in enumerate(P9.U3)}}; r = {}
        for L in (1, 2, 3):
            S = P9.build([dec] * L); r[f'Y{L}'] = lmin(S['H'])
            _, pc = P9.plaquettes(S); r[f'plaquette_classes_L{L}'] = P9.class_counts(pc)
            if L == 3: r['shadow_bottoms_T3'] = [lmin(SH.shadow_scalar(S, k)) for k in range(3)]
        r['legal_1star_types'] = len(C.legal_types(d)[0]); out[name] = r
    return out

if __name__ == '__main__' and len(sys.argv) > 1 and sys.argv[1] == 'profile':
    d = json.load(open(os.path.join(RES, 'phase12_orbit.json'))); d['profile'] = orbit_profile()
    json.dump(d, open(os.path.join(RES, 'phase12_orbit.json'), 'w'), indent=1, default=lambda o: o.item() if hasattr(o, 'item') else str(o))
    print(json.dumps(d['profile'], indent=1)); sys.exit(0)

if __name__ == '__main__' and len(sys.argv) > 1 and sys.argv[1] == 'closure':
    d = json.load(open(os.path.join(RES, 'phase12_orbit.json'))); d['closure'] = closure()
    json.dump(d, open(os.path.join(RES, 'phase12_orbit.json'), 'w'), indent=1, default=lambda o: o.item() if hasattr(o, 'item') else str(o))
    print(json.dumps(d['closure'], indent=1)); sys.exit(0)

if __name__ == '__main__' and len(sys.argv) > 1 and sys.argv[1] == 'defect':
    d = json.load(open(os.path.join(RES, 'phase12_orbit.json'))); d['defect_law'] = defect_law()
    json.dump(d, open(os.path.join(RES, 'phase12_orbit.json'), 'w'), indent=1, default=lambda o: o.item() if hasattr(o, 'item') else str(o))
    print(json.dumps(d['defect_law'], indent=1)); sys.exit(0)

if __name__ == '__main__':
    os.environ.setdefault('OMP_NUM_THREADS', '1')
    path = os.path.join(RES, 'phase12_orbit.json'); out = json.load(open(path)) if os.path.exists(path) else {}
    out.update({'lemma': lemma(), 'funnel': funnel()})                     # merge: keeps the 'defect_law' entry
    json.dump(out, open(path, 'w'), indent=1, default=lambda o: o.item() if hasattr(o, 'item') else str(o))
    print(json.dumps(out, indent=1, default=str)[:4000])
