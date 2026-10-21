"""
phase5a_recursion_theorem_audit.py -- the type-substitution recursion as a theorem, and the clean-spectrum
criterion (research target H6).

Run from the repository root:
    python3 -u -I audit/phase5a_recursion_theorem_audit.py            # full run (~6-8 min, < 1.5 GB)
    python3 -u -I audit/phase5a_recursion_theorem_audit.py --fast     # skips the achiral / random decorations
Output: audit/results/phase5a_recursion_theorem_audit.txt (everything printed is also written there).

All arithmetic is exact (Python integers, sympy Rational / Poly over ZZ).  Nothing is fitted and no saved number is
used as input: the operator is rebuilt from the type images by exec-loading audit/phase4_type_substitution_proof.py
(exactly as audit/export_type_certificate.py does), the finite-size counts are re-enumerated from the geometry, and
the certificate vectors are parsed from certificates/TypeSubstitutionCertificate.lean AND recomputed.

CONVENTION (stated once, verified in Section 1 below)
-----------------------------------------------------
Type-count vectors are COLUMN vectors:  v_m = (P_m ; Pi_m) in Z^{49+108} = Z^157, P_m(t) = number of inter-tile
panels of type t in the level-m supertile T_m, Pi_m(theta) = number of inter-tile plaquettes of type theta.
The type-substitution operator is S = [[M, 0], [A, B]] with

    S[r, c] = number of FINE objects of type r produced by ONE COARSE object of type c,

i.e. columns are indexed by the coarse (parent) type and rows by the fine (child) type.  Consequently
    * every column of M sums to 4   (an inflated panel is covered by a 2x2 grid of 4 fine panels),
    * every column of A sums to 4   (the 2x2 grid has 2*2*(2-1) = 4 interior fine edges, each of which is a fine
                                     inter-tile plaquette because the fine cubes on the two sides belong to
                                     children of two different coarse tiles),
    * every column of B sums to 2   (an inflated lattice edge consists of 2 fine edges),
and the ROW sums are NOT constant: the row sum of r counts, with multiplicity, how many coarse types produce a fine
object of type r, which depends on r.

THE AFFINE RECURSION AND WHY ITS THREE TERMS ARE EXHAUSTIVE AND DISJOINT (parity trichotomy)
--------------------------------------------------------------------------------------------
T_{m+1} = sigma(T_m) is the dilate by 2 of T_m: the coarse unit cube with lower corner x in Z^3 is replaced by the
8 fine cubes with lower corners 2x + {0,1}^3, all of which belong to children of the coarse tile owning x (exact
self-replication of the chair under the FR30 rule).  Hence the coarse parent of a fine cube c is floor(c/2).

Panels.  A fine inter-tile panel is a unit face between fine cubes c and c + e_ax owned by different fine tiles.
Their coarse parents floor(c/2), floor((c+e_ax)/2) are either the same coarse cube (c_ax even) or two coarse cubes
adjacent in direction ax (c_ax odd).  If the two coarse parents belong to the SAME coarse tile t, the fine panel is
interior to sigma(t), which by equivariance is a rigid copy of T_1; the 8^m coarse tiles of T_m contribute exactly
8^m p_1 (p_1 = panel-type vector of T_1).  Otherwise the two coarse parents are adjacent cubes of two different coarse
tiles, so they share a coarse inter-tile panel, and the fine panel is one of the 4 fine panels covering it: this is
the term M P_m.  The two cases are disjoint (same tile / different tiles) and exhaustive.

Plaquettes.  A fine plaquette is a fine lattice edge e in direction k whose 4 surrounding fine cubes are present and
belong to >= 2 fine tiles.  Let mu be the midpoint of e: mu_k is a half-integer and mu_i, mu_j (the other two
coordinates) are integers.  The 4 fine cubes have lower corners mu - e_k/2 - eps_i e_i - eps_j e_j, eps in {0,1},
so in direction i their coordinates are mu_i - 1 and mu_i, whose halves floor((mu_i-1)/2), floor(mu_i/2) coincide
iff mu_i is odd (same for j); in direction k all four share the coordinate floor(mu_k - 1/2), hence one coarse value.
So the set of coarse parent cubes has size 1, 2 or 4 according to whether (mu_i, mu_j) has 2, 1 or 0 odd entries,
and these three cases are exhaustive and mutually exclusive (a parity pattern of (mu_i, mu_j) is exactly one of
odd/odd, odd/even or even/odd, even/even).  Geometrically mu/2 lies, respectively, in the interior of a coarse cube,
in the interior of a coarse face (on its mid-line), or on a coarse edge.
  (1) If all coarse parents lie in ONE coarse tile t (this always happens in the size-1 case and may happen in the
      size-2 and size-4 cases), e is interior to sigma(t), a rigid copy of T_1: these edges contribute exactly
      8^m pi_1 (pi_1 = plaquette-type vector of T_1; by equivariance each sigma(t) contributes exactly pi_1, which
      is verified tile by tile below).
  (2) Otherwise, if there are 2 coarse parents, they are adjacent cubes of two different coarse tiles, hence share
      a coarse inter-tile panel, and e is one of the 4 interior fine edges of the 2x2 grid covering that panel:
      the term A P_m.
  (3) Otherwise there are 4 coarse parents around a coarse edge, all present (their children are), belonging to
      >= 2 coarse tiles, i.e. the coarse edge is a coarse inter-tile plaquette and e is one of its 2 fine halves:
      the term B Pi_m.
Therefore, exactly,  P_{m+1} = 8^m p_1 + M P_m  and  Pi_{m+1} = 8^m pi_1 + A P_m + B Pi_m,  i.e.
v_{m+1} = S v_m + 8^m f with f = (p_1 ; pi_1).  Section 2 below verifies every one of these category identities,
not just their sum, against the directly enumerated supertiles at levels 1..4.

CLEAN-SPECTRUM CRITERION (Section 4; proof in deliverables/PHASE5A_RECURSION_THEOREM.md)
--------------------------------------------------------------------------------------
Let M be a nonnegative integer matrix with constant column sums K >= 2 and let G be the directed type graph
(edge c -> r iff M[r, c] > 0).  Write M_C for the principal submatrix on a strongly connected component C.
  * charpoly(M) = prod_C charpoly(M_C)  (Frobenius normal form: condensation order makes M block triangular).
  * C is a SINK (closed under inflation) iff all column sums of M_C equal K; then rho(M_C) = K is a simple
    eigenvalue of M_C.  If C is not a sink then rho(M_C) < K.   Hence mult_M(K) = number of sink components.
  * For a NON-SINK component C:  spec(M_C) is contained in {0, 1, K} iff C is a single node with self-loop weight
    0 (transient type) or 1 (weight-1 fixed point).  [If |C| >= 2, M_C is irreducible with every column sum >= 1;
    if the column sums are not all equal then min < rho < max <= K, and min >= 1 so rho is not in {0,1,K};
    if they are all equal to s then rho = s in {1,...,K-1}, and s = 1 forces M_C to be a permutation matrix of a
    single cycle of length |C| >= 2 whose spectrum contains a non-trivial root of unity.]
  * For a SINK component the nonzero spectrum is {K} union (non-Perron part); it is contained in {1, K} iff the
    non-Perron eigenvalues of M_C lie in {0, 1} (in particular M_C must be primitive).  This holds automatically
    when the sink is a single node (M[c, c] = K: self-reproducing type).
THEOREM.  nonzero spec(M) is contained in {1, K}  iff  (i) every non-sink SCC is a single node with self-loop
0 or 1 and (ii) every sink SCC has non-Perron spectrum in {0, 1}.  A sufficient condition for (ii) is that every
sink SCC is a single node.  The same statement holds for B with K = 2 and for S = [[M,0],[A,B]] (spec S = spec M
union spec B).  Section 4 checks every clause of this theorem on every SCC of every decoration analysed.
"""
import os, sys, io, re, time, contextlib, collections, itertools
import numpy as np, sympy as sp
from sympy.polys.matrices import DomainMatrix
from sympy import ZZ, QQ

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..'))
RESULTS = os.path.join(HERE, 'results')
LEAN = os.path.join(ROOT, 'certificates', 'TypeSubstitutionCertificate.lean')
sys.path.insert(0, HERE)
lam = sp.Symbol('lambda')

_OUT = [None]
def log(*a, **k):
    s = ' '.join(str(x) for x in a)
    print(s, **k, flush=True)
    if _OUT[0] is not None:
        _OUT[0].write(s + '\n'); _OUT[0].flush()

# ----------------------------------------------------------------------------------------------------------------
# generic exact linear algebra helpers
# ----------------------------------------------------------------------------------------------------------------
def dm(Mat):
    return DomainMatrix.from_Matrix(sp.Matrix(Mat)).convert_to(ZZ)

def charpoly_expr(Mat):
    """Exact characteristic polynomial (monic, variable lambda) via fraction-free DomainMatrix arithmetic."""
    coeffs = dm(Mat).charpoly()
    return sp.Poly([int(c) for c in coeffs], lam).as_expr()

def rank_exact(Mat):
    return dm(Mat).convert_to(QQ).rank()

def colsums(Mat):
    return [sum(Mat[:, j]) for j in range(Mat.shape[1])]

def rowsums(Mat):
    return [sum(Mat[i, :]) for i in range(Mat.shape[0])]

def factor_set(cp):
    return sorted({str(f) for f, _ in sp.factor_list(cp, lam)[1]})

def root_mult(cp, a):
    """Multiplicity of the integer root a in the polynomial cp (0 if a is not a root)."""
    P = sp.Poly(cp, lam); k = 0
    while P.degree() > 0 and P.eval(a) == 0:
        P = sp.Poly(sp.quo(P.as_expr(), lam - a, lam), lam); k += 1
    return k

def is_clean(cp, allowed):
    """True iff every irreducible factor of cp is lambda or lambda - a for a in allowed."""
    return all(f in [lam] + [lam - a for a in allowed] for f, _ in sp.factor_list(cp, lam)[1])

# ----------------------------------------------------------------------------------------------------------------
# strongly connected components (Tarjan) of the type graph  c -> r  iff  Mat[r, c] > 0
# ----------------------------------------------------------------------------------------------------------------
def sccs(Mat):
    n = Mat.shape[0]
    adj = [[r for r in range(n) if Mat[r, c] != 0] for c in range(n)]
    sys.setrecursionlimit(max(10000, sys.getrecursionlimit()))
    index, low, onstack, stack, comps, cnt = {}, {}, set(), [], [], [0]
    def strong(v):
        index[v] = low[v] = cnt[0]; cnt[0] += 1; stack.append(v); onstack.add(v)
        for w in adj[v]:
            if w not in index:
                strong(w); low[v] = min(low[v], low[w])
            elif w in onstack:
                low[v] = min(low[v], index[w])
        if low[v] == index[v]:
            comp = []
            while True:
                w = stack.pop(); onstack.discard(w); comp.append(w)
                if w == v: break
            comps.append(sorted(comp))
    for v in range(n):
        if v not in index: strong(v)
    return comps          # Tarjan order: a component is emitted after everything reachable from it (sinks first)

def analyse_blocks(Mat, K, label, type_desc=None, list_types=True):
    """Condensation of the type graph of Mat (constant column sums K); per-SCC block spectrum and the theorem's
    clauses.  Returns a dict with the verified facts."""
    n = Mat.shape[0]
    cs = colsums(Mat); assert all(s == K for s in cs), (label, 'column sums', collections.Counter(cs))
    comps = sccs(Mat)
    cp_full = charpoly_expr(Mat)
    prod = sp.Integer(1); rows = []
    for C in comps:
        Bk = Mat.extract(C, C); k = len(C)
        cp = charpoly_expr(Bk); prod *= cp
        bcs = colsums(Bk); sink = all(s == K for s in bcs)
        facs = sp.factor_list(cp, lam)[1]
        clean = is_clean(cp, (1, K))
        if k == 1:
            loop = int(Bk[0, 0])
            if loop == 0: kind = 'transient singleton (loop 0)'
            elif loop == 1: kind = 'fixed-point singleton (loop 1)'
            elif loop == K: kind = f'self-reproducing sink singleton (loop {K})'
            else: kind = f'NON-CLEAN singleton with loop {loop}'
            pred = (loop in (0, 1, K))
        else:
            is_perm = all(s == 1 for s in bcs) and all(s == 1 for s in rowsums(Bk))
            if is_perm: kind = f'cycle of length {k} (permutation block)'
            elif sink: kind = f'irreducible SINK block of size {k}'
            else: kind = f'irreducible non-sink block of size {k}'
            pred = (None if sink else False)
        # Perron root check: K must be a simple root of a sink block's charpoly and no root of a non-sink block's
        multK = root_mult(cp, K)
        nonperron_clean = is_clean(sp.cancel(cp / (lam - K) ** multK), (1,))
        rk, tr = rank_exact(Bk), int(Bk.trace())
        # rank test for sink blocks: a rank-r block has at most r nonzero eigenvalues, one of which is K;
        # rank 1 -> spectrum {K, 0}: clean;  rank 2 -> the other nonzero eigenvalue is trace - K, clean iff trace in {K, K+1}
        rank_pred = (True if rk == 1 else (tr - K in (0, 1) if rk == 2 else None)) if (sink and k > 1) else None
        rows.append(dict(nodes=C, k=k, sink=sink, kind=kind, cp=sp.factor(cp), factors=factor_set(cp), clean=clean,
                         pred=pred, colsums=bcs, multK=multK, nonperron_clean=nonperron_clean, rank=rk, trace=tr, rank_pred=rank_pred))
    assert sp.expand(prod - cp_full) == 0, 'product of SCC block charpolys != charpoly'
    n_sink = sum(1 for r in rows if r['sink'])
    multK_full = root_mult(cp_full, K)
    clean_full = is_clean(cp_full, (1, K))
    clean_all_blocks = all(r['clean'] for r in rows)
    # theorem clauses
    clause_i = all(r['k'] == 1 and int(Mat[r['nodes'][0], r['nodes'][0]]) in (0, 1) for r in rows if not r['sink'])
    clause_ii = all(r['nonperron_clean'] for r in rows if r['sink'])
    pred_ok = all(r['pred'] is None or r['pred'] == r['clean'] for r in rows)
    rank_pred_ok = all(r['rank_pred'] is None or r['rank_pred'] == r['clean'] for r in rows)
    sink_simple = all(r['multK'] == 1 for r in rows if r['sink']) and all(r['multK'] == 0 for r in rows if not r['sink'])
    kinds = collections.Counter(r['kind'] for r in rows)
    log(f"\n[{label}]  n={n}  K={K}  #SCC={len(rows)}  #sink SCC={n_sink}")
    log(f"   charpoly = {sp.factor(cp_full)}")
    log(f"   charpoly == product of SCC block charpolys: True")
    log(f"   multiplicity of eigenvalue {K} = {multK_full}  ==  number of sink SCCs = {n_sink}: {int(multK_full) == n_sink}")
    log(f"   Perron root {K} simple in every sink block and absent from every non-sink block: {sink_simple}")
    log(f"   nonzero spectrum contained in {{1,{K}}}: {clean_full};  every SCC block clean: {clean_all_blocks};  iff holds: {clean_full == clean_all_blocks}")
    log(f"   THEOREM clauses: (i) every non-sink SCC is a singleton with loop 0/1: {clause_i};  (ii) every sink SCC has non-Perron spectrum in {{0,1}}: {clause_ii};"
        f"  (i) and (ii) <=> clean: {(clause_i and clause_ii) == clean_full}")
    log(f"   per-SCC theorem predictions agree with computed block spectra: {pred_ok};  rank-1/rank-2 sink-block predictions agree: {rank_pred_ok}")
    log(f"   SCC kinds: {dict(kinds)}")
    for r in rows:
        if r['k'] > 1 or not r['clean'] or r['sink']:
            desc = ''
            if type_desc is not None and r['k'] == 1: desc = '  ' + type_desc(r['nodes'][0])
            extra = f"; rank {r['rank']}, trace {r['trace']}" if r['k'] > 1 else ''
            log(f"     SCC {r['nodes']}: {r['kind']}; block charpoly {r['cp']}; column sums {r['colsums']}{extra}; clean={r['clean']}{desc}")
            if r['k'] > 1 and r['sink']:
                Bk = Mat.extract(r['nodes'], r['nodes'])
                log(f"       block matrix (rows/cols in the listed order): {Bk.tolist()}")
    loops = collections.Counter(int(Mat[i, i]) for i in range(n))
    log(f"   self-loop weights Mat[c,c] histogram: {dict(sorted(loops.items()))}  (types with Mat[c,c] = {K}: {[i for i in range(n) if Mat[i, i] == K]})")
    if list_types:
        for kind in sorted(kinds):
            idx = sorted(itertools.chain.from_iterable(r['nodes'] for r in rows if r['kind'] == kind))
            log(f"     {kind}: {len(idx)} types: {idx}")
    # where do the non-clean factors come from?
    nonclean = collections.defaultdict(list)
    for r in rows:
        for f in r['factors']:
            if f not in ('lambda', 'lambda - 1', f'lambda - {K}'):
                nonclean[f].append(r['kind'])
    if nonclean:
        log("   origin of each non-clean irreducible factor:")
        for f, ks in sorted(nonclean.items()):
            log(f"     {f}: from {dict(collections.Counter(ks))}")
    return dict(cp=cp_full, rows=rows, n_sink=n_sink, multK=int(multK_full), clean=clean_full, clean_blocks=clean_all_blocks,
                clause_i=clause_i, clause_ii=clause_ii, pred_ok=pred_ok, rank_pred_ok=rank_pred_ok, sink_simple=sink_simple, kinds=kinds, nonclean=dict(nonclean))

# ----------------------------------------------------------------------------------------------------------------
# certificate parsing (certificates/TypeSubstitutionCertificate.lean)
# ----------------------------------------------------------------------------------------------------------------
def parse_lean_lists(path=LEAN):
    with open(path) as fh: txt = fh.read()
    out = {}
    for name, body in re.findall(r"^def (\w+) : List Int := \[(.*?)\]\s*$", txt, re.M):
        out[name] = [int(x) for x in body.split(',')] if body.strip() else []
    for name, body in re.findall(r"^def (\w+) : List Nat := \[(.*?)\]\s*$", txt, re.M):
        out[name] = [int(x) for x in body.split(',')] if body.strip() else []
    for name, body in re.findall(r"^def (\w+) : List \(List Nat\) := \[(.*?)\]\s*$", txt, re.M):
        out[name] = [[int(x) for x in grp.split(',')] for grp in re.findall(r"\[([^\[\]]*)\]", body)]
    for name, val in re.findall(r"^def (D|NP|NQ|N) : (?:Int|Nat) := (\d+)\s*$", txt, re.M):
        out[name] = int(val)
    return out

def S_from_certificate(cert):
    nP, nQ = cert['NP'], cert['NQ']; N = nP + nQ
    S = sp.zeros(N, N)
    for c, lst in enumerate(cert['panelImgP']):
        for r in lst: S[r, c] += 1
    for c, lst in enumerate(cert['panelImgQ']):
        for r in lst: S[nP + r, c] += 1
    for c, lst in enumerate(cert['plaqImg']):
        for r in lst: S[nP + r, nP + c] += 1
    f = sp.Matrix(cert['seedPCert'] + cert['seedQCert'])
    return S, f, nP, nQ

def recursion_vectors(S, f, mmax):
    """v_1 = f, v_{m+1} = S v_m + 8^m f, exact integers; returns {m: list[int]}."""
    Sl = [[int(S[i, j]) for j in range(S.shape[1])] for i in range(S.shape[0])]
    fl = [int(x) for x in f]; v = {1: fl[:]}
    for m in range(1, mmax):
        cur = v[m]
        v[m + 1] = [sum(Sl[i][j] * cur[j] for j in range(len(cur)) if Sl[i][j]) + 8**m * fl[i] for i in range(len(cur))]
    return v

# ----------------------------------------------------------------------------------------------------------------
# Section 1-2: rebuild the operator from the phase-4 type images, re-enumerate the supertiles by category
# ----------------------------------------------------------------------------------------------------------------
def load_phase4():
    src = open(os.path.join(HERE, 'phase4_type_substitution_proof.py')).read()
    src = src.split("# ---------------- exact spectral analysis")[0]
    ns = {"__name__": "p4", "__file__": os.path.join(HERE, "phase4_type_substitution_proof.py")}
    with contextlib.redirect_stdout(io.StringIO()):
        exec(compile(src, "phase4", "exec"), ns)
    return ns

def build_S(ns):
    ptypes, qtypes = ns['ptypes_all'], ns['qtypes_all']
    ip = {t: n for n, t in enumerate(ptypes)}; iq = {t: n for n, t in enumerate(qtypes)}
    nP, nQ = len(ptypes), len(qtypes)
    M = sp.zeros(nP, nP); A = sp.zeros(nQ, nP); B = sp.zeros(nQ, nQ)
    for t in ptypes:
        for tt, mlt in ns['panel_img'][t].items(): M[ip[tt], ip[t]] += mlt            # row = fine, col = coarse
        for tt, mlt in ns['plaq_img_from_panel'][t].items(): A[iq[tt], ip[t]] += mlt
    for t in qtypes:
        for tt, mlt in ns['plaq_img'][t].items(): B[iq[tt], iq[t]] += mlt
    S = sp.BlockMatrix([[M, sp.zeros(nP, nQ)], [A, B]]).as_explicit()
    f = sp.Matrix([ns['P1'].get(t, 0) for t in ptypes] + [ns['Pi1'].get(t, 0) for t in qtypes])
    return M, A, B, S, f, ptypes, qtypes, ip, iq

def tiling_poses(ns, m):
    poses = [(np.eye(3, dtype=int), np.zeros(3, dtype=int))]
    for _ in range(m): poses = ns['inflate_config'](poses)
    return poses

def enumerate_level_by_category(ns, m, ip, iq):
    """Direct enumeration of T_m with every inter-tile panel / plaquette assigned to its parity category relative to
    T_{m-1}.  Returns category -> (panel vector, plaquette vector) as integer lists, plus per-coarse-tile seeds."""
    owner_map, panel_type, ptc, pcubes, key, E = (ns[k] for k in ('owner_map', 'panel_type', 'plaquette_type_and_class', 'plaquette_cubes', 'key', 'E'))
    om = owner_map(tiling_poses(ns, m)); omc = owner_map(tiling_poses(ns, m - 1))
    nP, nQ = len(ip), len(iq)
    P = {c: [0] * nP for c in ('tile', 'panel')}; Q = {c: [0] * nQ for c in ('tile', 'panel', 'edge')}
    per_tile_P = collections.defaultdict(lambda: [0] * nP); per_tile_Q = collections.defaultdict(lambda: [0] * nQ)
    classes = collections.Counter()
    for c, pose in om.items():
        ca = np.array(c)
        for ax in range(3):
            c2 = tuple(ca + E[ax])
            if c2 in om and key(*om[c2]) != key(*pose):
                t = panel_type(om, c, ax); assert t in ip, 'panel type outside the closed system'
                k1, k2 = key(*omc[tuple(ca // 2)]), key(*omc[tuple(np.array(c2) // 2)])
                if k1 == k2:
                    P['tile'][ip[t]] += 1; per_tile_P[k1][ip[t]] += 1
                else:
                    assert tuple(ca // 2) != tuple(np.array(c2) // 2)
                    P['panel'][ip[t]] += 1
        for (i, j) in ((0, 1), (0, 2), (1, 2)):
            cs = pcubes(c, i, j)
            if all(x in om for x in cs):
                t, cl = ptc(om, c, i, j)
                if t is None: continue
                assert t in iq, 'plaquette type outside the closed system'
                classes[cl] += 1
                coarse = {tuple(np.array(x) // 2) for x in cs}
                ckeys = {key(*omc[x]) for x in coarse}
                assert len(coarse) in (1, 2, 4), coarse
                if len(ckeys) == 1:
                    Q['tile'][iq[t]] += 1; per_tile_Q[next(iter(ckeys))][iq[t]] += 1
                elif len(coarse) == 2:
                    a, b = sorted(coarse); assert sum(abs(np.array(a) - np.array(b))) == 1   # adjacent coarse cubes
                    Q['panel'][iq[t]] += 1
                else:
                    assert all(x in omc for x in coarse) and len(ckeys) >= 2
                    Q['edge'][iq[t]] += 1
    return P, Q, dict(per_tile_P), dict(per_tile_Q), classes, len(om) // 7

def run_sections_1_2(ns, M, A, B, S, f, ptypes, qtypes, ip, iq, maxlevel=4):
    nP, nQ = len(ptypes), len(qtypes); N = nP + nQ
    log("=" * 100); log("SECTION 1.  THE OPERATOR S = [[M, 0], [A, B]] REBUILT FROM THE TYPE IMAGES (convention: S[r,c] = #fine type r per coarse type c)")
    log(f" sizes: M {M.shape}, A {A.shape}, B {B.shape}, S {S.shape};  seed f = (p1 ; pi1) with sum(p1) = {sum(f[:nP])}, sum(pi1) = {sum(f[nP:])}")
    for name, X, K in (('M', M, 4), ('A', A, 4), ('B', B, 2)):
        cs = collections.Counter(int(x) for x in colsums(X)); rs = collections.Counter(int(x) for x in rowsums(X))
        log(f" column sums of {name}: {dict(cs)}  -> all equal to {K}: {set(cs) == {K}}")
        log(f" row sums of {name}:    {dict(sorted(rs.items()))}  (not constant: {len(rs) > 1}; min {min(rs)}, max {max(rs)})")
    assert set(int(x) for x in colsums(M)) == {4} and set(int(x) for x in colsums(A)) == {4} and set(int(x) for x in colsums(B)) == {2}
    log(f" S is block lower triangular: upper-right block identically zero: {S[:nP, nP:] == sp.zeros(nP, nQ)}")
    log(f" entries of S are nonnegative integers: {all(int(x) >= 0 for x in S)};  number of nonzero entries: {sum(1 for x in S if x != 0)}")

    log("\n" + "=" * 100); log("SECTION 2.  THE AFFINE FORCING TERM: DIRECT ENUMERATION OF T_1..T_%d BY PARITY CATEGORY" % maxlevel)
    seedP = [int(x) for x in f[:nP]]; seedQ = [int(x) for x in f[nP:]]
    Sl = [[int(S[i, j]) for j in range(N)] for i in range(N)]
    def matvec(Mat, v): return [sum(int(Mat[i, j]) * v[j] for j in range(Mat.shape[1]) if Mat[i, j] != 0) for i in range(Mat.shape[0])]
    direct = {}; ok_all = True
    for m in range(1, maxlevel + 1):
        t0 = time.time()
        P, Q, ptP, ptQ, classes, ntiles = enumerate_level_by_category(ns, m, ip, iq)
        Ptot = [a + b for a, b in zip(P['tile'], P['panel'])]; Qtot = [a + b + c for a, b, c in zip(Q['tile'], Q['panel'], Q['edge'])]
        direct[m] = Ptot + Qtot
        cls = {c: classes.get(c, 0) for c in ('1', '-1', 'i', 'j', 'k')}
        log(f"\n level {m}: {ntiles} tiles, {sum(Ptot)} inter-tile panels, {sum(Qtot)} inter-tile plaquettes, classes {cls}  ({time.time() - t0:.0f}s)")
        log(f"   category sizes: panels tile/panel = {sum(P['tile'])}/{sum(P['panel'])};  plaquettes tile/panel/edge = {sum(Q['tile'])}/{sum(Q['panel'])}/{sum(Q['edge'])}")
        ncoarse = 8 ** (m - 1)
        c1 = P['tile'] == [ncoarse * x for x in seedP]; c2 = Q['tile'] == [ncoarse * x for x in seedQ]
        pt_ok = len(ptP) == ncoarse and len(ptQ) == ncoarse and all(v == seedP for v in ptP.values()) and all(v == seedQ for v in ptQ.values())
        log(f"   (1) interior-of-inflated-tile panels == 8^{m-1} * p1: {c1};  plaquettes == 8^{m-1} * pi1: {c2};  EVERY one of the {ncoarse} inflated coarse tiles contributes exactly (p1, pi1): {pt_ok}")
        ok_all &= c1 and c2 and pt_ok
        if m >= 2:
            Pprev, Qprev = direct[m - 1][:nP], direct[m - 1][nP:]
            c3 = P['panel'] == matvec(M, Pprev); c4 = Q['panel'] == matvec(A, Pprev); c5 = Q['edge'] == matvec(B, Qprev)
            c6 = direct[m] == [a + 8 ** (m - 1) * b for a, b in zip(matvec(S, direct[m - 1]), seedP + seedQ)]
            log(f"   (2) fine panels covering inflated panels == M P_{m-1}: {c3};  (2') interior edges of inflated panels == A P_{m-1}: {c4};  (3) halves of inflated edges == B Pi_{m-1}: {c5}")
            log(f"   TOTAL: v_{m} == 8^{m-1} f + S v_{m-1} exactly (all {N} coordinates): {c6}")
            ok_all &= c3 and c4 and c5 and c6
    log(f"\n ALL category identities and the recursion v_(m+1) = 8^m f + S v_m hold exactly for m = 1..{maxlevel - 1}: {ok_all}")
    return direct, ok_all

# ----------------------------------------------------------------------------------------------------------------
# Section 3: exact spectral structure and closed form
# ----------------------------------------------------------------------------------------------------------------
def run_section_3(M, B, S, f, nP, nQ):
    N = nP + nQ
    log("\n" + "=" * 100); log("SECTION 3.  EXACT SPECTRUM, SEMISIMPLICITY, NILPOTENCY INDEX, CLOSED FORM")
    cpM, cpB, cpS = charpoly_expr(M), charpoly_expr(B), charpoly_expr(S)
    expM = lam**44 * (lam - 4) * (lam - 1)**4; expB = lam**103 * (lam - 2) * (lam - 1)**4
    log(f" charpoly(M) = {sp.factor(cpM)}   == lambda^44 (lambda-4)(lambda-1)^4: {sp.expand(cpM - expM) == 0}")
    log(f" charpoly(B) = {sp.factor(cpB)}   == lambda^103 (lambda-2)(lambda-1)^4: {sp.expand(cpB - expB) == 0}")
    log(f" charpoly(S) = {sp.factor(cpS)}   == charpoly(M) * charpoly(B): {sp.expand(cpS - cpM * cpB) == 0}")
    res = dict(cpM_ok=sp.expand(cpM - expM) == 0, cpB_ok=sp.expand(cpB - expB) == 0, cpS_ok=sp.expand(cpS - cpM * cpB) == 0)
    I = sp.eye(N); semis = {}
    for ev, alg in ((4, 1), (2, 1), (1, 8)):
        r1 = rank_exact(S - ev * I); r2 = rank_exact((S - ev * I) ** 2)
        geo = N - r1; semis[ev] = (geo == alg and r1 == r2)
        log(f" eigenvalue {ev}: algebraic multiplicity {alg}, geometric multiplicity N - rank(S-{ev}) = {geo}, rank(S-{ev}) = rank((S-{ev})^2) = {r1 == r2} -> semisimple: {semis[ev]}")
    r1, r2, r3 = rank_exact(S), rank_exact(S ** 2), rank_exact(S ** 3)
    nil2 = (r1 > r2) and (r2 == r3) and (N - r2 == 147)
    log(f" eigenvalue 0: algebraic multiplicity 147; rank S = {r1}, rank S^2 = {r2}, rank S^3 = {r3} -> nilpotency index of the 0-part = 2: {nil2}  (dim generalized 0-eigenspace = N - rank S^2 = {N - r2})")
    res['semisimple'] = all(semis.values()); res['nilp2'] = nil2

    cert = parse_lean_lists()
    D = cert['D']; W = {8: cert['W8L'], 4: cert['W4L'], 2: cert['W2L'], 1: cert['W1L']}
    log(f"\n certificate parsed from {os.path.relpath(LEAN, ROOT)}: D = {D}, NP = {cert['NP']}, NQ = {cert['NQ']}, |W8| = {len(W[8])}, |W4| = {len(W[4])}, |W2| = {len(W[2])}, |W1| = {len(W[1])}")
    assert cert['NP'] == nP and cert['NQ'] == nQ and all(len(w) == N for w in W.values())
    # certificate images rebuild the same operator?
    Sc, fc, _, _ = S_from_certificate(cert)
    log(f" S rebuilt from the certificate index lists (panelImgP/panelImgQ/plaqImg) == S rebuilt from the phase-4 type images: {Sc == S};  seed lists == f: {fc == f}")
    res['cert_S_ok'] = (Sc == S and fc == f)
    # recompute W independently: W8 = D (8 - S)^{-1} f; W4, W2, W1 from v_3, v_4, v_5 (Vandermonde), as eigen-certificate
    v = recursion_vectors(S, f, 9)
    W8r = (8 * I - S).LUsolve(f)
    rhs = [sp.Matrix(v[m]) - 8 ** m * W8r for m in (3, 4, 5)]
    Vinv = sp.Matrix([[64, 8, 1], [256, 16, 1], [1024, 32, 1]]).inv()
    W4r = Vinv[0, 0] * rhs[0] + Vinv[0, 1] * rhs[1] + Vinv[0, 2] * rhs[2]
    W2r = Vinv[1, 0] * rhs[0] + Vinv[1, 1] * rhs[1] + Vinv[1, 2] * rhs[2]
    W1r = Vinv[2, 0] * rhs[0] + Vinv[2, 1] * rhs[1] + Vinv[2, 2] * rhs[2]
    Drec = 1
    for Wv in (W8r, W4r, W2r, W1r):
        for x in Wv: Drec = sp.ilcm(Drec, sp.Rational(x).q)
    log(f" recomputed common denominator of ((8-S)^-1 f, W4, W2, W1) = {Drec}  == certificate D = {D}: {int(Drec) == D}")
    match = {k: [int(D * x) for x in Wv] == W[k] for k, Wv in ((8, W8r), (4, W4r), (2, W2r), (1, W1r))}
    log(f" recomputed D*W vectors equal the parsed certificate lists: {match}")
    SW = {k: sp.Matrix(W[k]) for k in W}
    eig_ok = dict(W8=(S * SW[8] + D * f == 8 * SW[8]), W4=(S * SW[4] == 4 * SW[4]), W2=(S * SW[2] == 2 * SW[2]), W1=(S * SW[1] == SW[1]))
    log(f" eigen-identities of the parsed vectors: S W8 + D f = 8 W8: {eig_ok['W8']}; S W4 = 4 W4: {eig_ok['W4']}; S W2 = 2 W2: {eig_ok['W2']}; S W1 = W1: {eig_ok['W1']}")
    log(f" nonzero coordinates: W8 {sum(1 for x in W[8] if x)}, W4 {sum(1 for x in W[4] if x)}, W2 {sum(1 for x in W[2] if x)} (indices {[i for i, x in enumerate(W[2]) if x]}), W1 {sum(1 for x in W[1] if x)}")
    cf = {}
    for m in range(1, 10):
        cf[m] = all(D * v[m][i] == 8 ** m * W[8][i] + 4 ** m * W[4][i] + 2 ** m * W[2][i] + W[1][i] for i in range(N))
    log(f" closed form D v_m = 8^m W8 + 4^m W4 + 2^m W2 + W1 (D = {D}) holds exactly for m = 3..9: {all(cf[m] for m in range(3, 10))};  per level: {cf}")
    log(f"   reading: the closed form holds for every m >= 2 = nilpotency index of the 0-part (the Lean certificate proves m >= 3 from the base case v_3);")
    log(f"   it fails at m = 1 because (8-S)^-1 f_0 = (8 f_0 + S f_0)/64 differs from f_0/8 when S f_0 != 0 (f_0 = component of f in the generalized 0-eigenspace),")
    log(f"   while for m >= 2 the 0-part of v_m is 8^(m-2) (8 f_0 + S f_0) = 8^m (8-S)^-1 f_0, i.e. absorbed into the 8^m W8 term.")
    # consequences for totals and class counts
    cls = cert['plaqClassCert']
    tot = lambda Wv: sum(Wv[nP:])
    sgn = lambda q: ('+ ' if q >= 0 else '- ') + str(abs(sp.Rational(q, D)))
    log(f" totals: D*N_m = {tot(W[8])}*8^m + ({tot(W[4])})*4^m + {tot(W[2])}*2^m + ({tot(W[1])})  ->  N_m = {sp.Rational(tot(W[8]), D)}*8^m {sgn(tot(W[4]))}*4^m {sgn(tot(W[2]))}*2^m {sgn(tot(W[1]))}")
    names = ['+1', '-1', 'i', 'j', 'k']; freqs = {}
    for ci, nm in enumerate(names):
        a = sum(W[8][nP + q] for q in range(nQ) if cls[q] == ci)
        freqs[nm] = sp.Rational(a, tot(W[8]))
    log(f" limiting class frequencies from W8: {freqs}")
    log(f" direct check: v_7 class counts from recursion = {[sum(v[7][nP+q] for q in range(nQ) if cls[q] == ci) for ci in range(5)]} (phase4 saved: [19677945, 3325970, 4194300, 5963773, 4194300])")
    res.update(D=D, W_match=all(match.values()), eig_ok=all(eig_ok.values()), closed_form_3_9=all(cf[m] for m in range(3, 10)), cf=cf, freqs=freqs,
               totals=(tot(W[8]), tot(W[4]), tot(W[2]), tot(W[1])), v=v, cert=cert)
    return res

# ----------------------------------------------------------------------------------------------------------------
# Section 4: clean-spectrum criterion across decorations
# ----------------------------------------------------------------------------------------------------------------
def load_universality():
    """exec-load audit/phase5_universality_types.py up to its driver section, patching `analyse` to also return the
    matrices and type lists (the file itself is not modified)."""
    path = os.path.join(HERE, 'phase5_universality_types.py')
    src = open(path).read().split("ACHIRAL = {k: (0, 1, 2) for k in FR30}")[0]
    old = "    return cpM, cpB, freqs"
    assert src.count(old) == 1
    src = src.replace(old, "    return cpM, cpB, freqs, dict(M=M, A=A, B=B, pts=pts, qts=qts, qclass=qclass, P1=P1, Pi1=Pi1)")
    ns = {"__name__": "u5", "__file__": path}
    exec(compile(src, "universality", "exec"), ns)
    return ns

def describe_panel_type(t):
    loc, nrm, (R, s) = t
    return f"loc{loc} n{nrm} R{R} s{s}"

def run_section_4(M, B, ptypes, qtypes, fast=False):
    log("\n" + "=" * 100); log("SECTION 4.  CLEAN-SPECTRUM CRITERION (H6): CONDENSATION OF THE TYPE GRAPHS")
    out = {}
    out['FR30'] = dict(M=analyse_blocks(M, 4, 'FR30: panel block M', type_desc=lambda i: describe_panel_type(ptypes[i])),
                       B=analyse_blocks(B, 2, 'FR30: plaquette block B'))
    if fast:
        return out
    u = load_universality()
    U3, FR30, perm_mat = u['U3'], u['FR30'], u['perm_mat']
    ACHIRAL = {k: (0, 1, 2) for k in FR30}
    rng = np.random.default_rng(2026)      # same stream as audit/phase5_universality_types.py -> its decorations #0, #1
    even, odd = u['even'], u['odd']
    def random_dec():
        d = {'0': even[rng.integers(3)]}
        for v in U3: d[v] = (even if sum(v) % 2 == 0 else odd)[rng.integers(3)]
        return d
    decs = [('FR30 (universality engine, cross-check)', FR30), ('achiral (D_s only)', ACHIRAL), ('random admissible #0 (seed 2026)', random_dec()), ('random admissible #1 (seed 2026)', random_dec())]
    for name, dec in decs:
        t0 = time.time(); buf = io.StringIO()
        with contextlib.redirect_stdout(buf):
            cpM, cpB, freqs, data = u['analyse'](name, *u['chair_geometry'](dec))
        log(f"\n--- decoration: {name}  [{time.time() - t0:.0f}s]  perms: {dec}")
        log(f"   types: {len(data['pts'])} panel, {len(data['qts'])} plaquette;  charpoly M = {cpM};  charpoly B = {cpB}")
        log(f"   limiting frequencies: {freqs}")
        if name.startswith('FR30'):
            same = (data['M'] == M and data['B'] == B)
            log(f"   universality-engine M, B identical to the phase-4 rebuilt M, B: {same}")
            out['FR30']['engine_same'] = same
            continue
        resM = analyse_blocks(data['M'], 4, f'{name}: panel block M', list_types=False)
        resB = analyse_blocks(data['B'], 2, f'{name}: plaquette block B', list_types=False)
        out[name] = dict(M=resM, B=resB, cpM=cpM, cpB=cpB, freqs=freqs, dec=dec)
    return out

# ----------------------------------------------------------------------------------------------------------------
def main(argv):
    fast = '--fast' in argv
    os.makedirs(RESULTS, exist_ok=True)
    _OUT[0] = open(os.path.join(RESULTS, 'phase5a_recursion_theorem_audit.txt'), 'w')
    t0 = time.time()
    log(f"phase5a_recursion_theorem_audit.py  (fast={fast})  sympy {sp.__version__}  numpy {np.__version__}")
    ns = load_phase4()
    M, A, B, S, f, ptypes, qtypes, ip, iq = build_S(ns)
    log(f"phase-4 type system loaded in {time.time() - t0:.0f}s: {len(ptypes)} panel types, {len(qtypes)} plaquette types")
    direct, ok12 = run_sections_1_2(ns, M, A, B, S, f, ptypes, qtypes, ip, iq, maxlevel=4)
    res3 = run_section_3(M, B, S, f, len(ptypes), len(qtypes))
    res4 = run_section_4(M, B, ptypes, qtypes, fast=fast)
    log("\n" + "=" * 100); log("SUMMARY")
    log(f" S1 column sums (M:4, A:4, B:2) exact: True;  S2 recursion by category exact for levels 1..4: {ok12}")
    log(f" S3 charpolys: M {res3['cpM_ok']}, B {res3['cpB_ok']}, S=M*B {res3['cpS_ok']}; semisimple nonzero part: {res3['semisimple']}; nilpotency index 2: {res3['nilp2']}")
    log(f" S3 certificate: S from Lean lists == S: {res3['cert_S_ok']}; W recomputed == parsed: {res3['W_match']}; eigen-identities: {res3['eig_ok']}; closed form m=3..9: {res3['closed_form_3_9']}; D = {res3['D']}")
    for name, r in res4.items():
        if 'M' in r:
            log(f" S4 {name}: M clean={r['M']['clean']} (#sink={r['M']['n_sink']}, mult4={r['M']['multK']}, clauses i/ii {r['M']['clause_i']}/{r['M']['clause_ii']}, predictions ok {r['M']['pred_ok']});"
                f" B clean={r['B']['clean']} (#sink={r['B']['n_sink']}, mult2={r['B']['multK']}, clauses i/ii {r['B']['clause_i']}/{r['B']['clause_ii']}, predictions ok {r['B']['pred_ok']})")
    log(f" total time {time.time() - t0:.0f}s")
    _OUT[0].close()

if __name__ == '__main__':
    main(sys.argv[1:])
