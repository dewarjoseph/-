"""
Regression tests for the independent Clifford-Q8 audit (audit/*.py). These tests do NOT import src/; they pin
the numbers established in deliverables/CLIFFORD_Q8_END_TO_END_AUDIT.md and the Phase-2 research document.
Run:  python3 -m unittest tests/test_independent_audit_regression.py
"""
import os, sys, unittest, itertools, collections
import numpy as np
ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
sys.path.insert(0, os.path.join(ROOT, "audit"))
from independent_clifford_q8_audit import (U3, FR30, perm_mat, tiles_at_level, panel_edges, clifford_link, q8label,
                                           fundamental_cycle_holonomies, generated_subgroup, sdot, SIG)
import sympy as sp

def plaquettes(tiles):
    owner, edges = panel_edges(tiles); cubes = set(owner); cnt = collections.Counter()
    for c in cubes:
        for (i, j) in [(0, 1), (1, 2), (0, 2)]:
            ei = [0, 0, 0]; ei[i] = 1; ej = [0, 0, 0]; ej[j] = 1
            c1 = (c[0]+ei[0], c[1]+ei[1], c[2]+ei[2]); c2 = (c1[0]+ej[0], c1[1]+ej[1], c1[2]+ej[2]); c3 = (c[0]+ej[0], c[1]+ej[1], c[2]+ej[2])
            if c1 in cubes and c2 in cubes and c3 in cubes and len({owner[c], owner[c1], owner[c2], owner[c3]}) > 1:
                W = np.eye(2, dtype=complex)
                for x, y in ((c, c1), (c1, c2), (c2, c3), (c3, c)):
                    if owner[x] != owner[y]: W = W @ clifford_link(tiles[owner[x]][0], tiles[owner[y]][0], np.array(y) - np.array(x))
                cnt[q8label(W)] += 1
    return cnt

class TestLevel1Exact(unittest.TestCase):
    def setUp(self):
        self.tiles = tiles_at_level(FR30, 1); self.owner, self.edges = panel_edges(self.tiles)
        self.links = [clifford_link(self.tiles[a][0], self.tiles[b][0], nf) for a, b, nf, _, _ in self.edges]

    def test_geometry(self):
        self.assertEqual(len(self.tiles), 8); self.assertEqual(len(self.owner), 56); self.assertEqual(len(self.edges), 48)
        self.assertEqual(len(self.edges) - 8 + 1, 41)  # cyclomatic number, not 48 as published

    def test_laplacian_charpoly_exact(self):
        W = collections.Counter((min(a, b), max(a, b)) for a, b, _, _, _ in self.edges); L = sp.zeros(8, 8)
        for (a, b), w in W.items(): L[a, b] -= w; L[b, a] -= w; L[a, a] += w; L[b, b] += w
        lam = sp.Symbol('lambda')
        self.assertEqual(sp.expand((lam*sp.eye(8) - L).det() - lam*(lam-24)*(lam**2-30*lam+207)*(lam**2-21*lam+99)**2), 0)

    def test_links(self):
        c = collections.Counter(q8label(C) for C in self.links)
        self.assertEqual(c['-1'], 24); self.assertEqual(c['+1'], 6); self.assertEqual(sum(v for k, v in c.items() if k not in ('+1', '-1')), 18)
        self.assertNotIn('other', c)

    def test_holonomy_group_and_cycles(self):
        hol = fundamental_cycle_holonomies(8, self.edges, self.links)
        self.assertEqual(len(hol), 41); self.assertEqual(len(generated_subgroup(hol)), 8)
        cnt = collections.Counter(q8label(h) for h in hol); self.assertEqual(41 - cnt['+1'], 24)

    def test_plaquette_curvature(self):
        c = plaquettes(self.tiles); self.assertEqual(sum(c.values()), 60); self.assertEqual(c['+1'], 26); self.assertEqual(c['-1'], 3)
        self.assertEqual(sum(v for k, v in c.items() if k not in ('+1', '-1')), 31)

    def test_ambient_gauge_factorization_and_adjoint_V4(self):
        def rot_pi(v): a = np.abs(v).argmax(); R = -np.eye(3, dtype=int); R[a, a] = 1; return R
        V4 = {tuple(np.eye(3, dtype=int).ravel())} | {tuple(rot_pi(np.eye(3, dtype=int)[i]).ravel()) for i in range(3)}
        for (a, b, nf, _, _), C in zip(self.edges, self.links):
            Ma, Mb = self.tiles[a][0], self.tiles[b][0]; Vamb = Ma @ Mb.T; Rn = rot_pi(nf)
            self.assertIn(tuple((Vamb.T @ Rn @ Vamb @ Rn).ravel()), V4)
            ub = Mb.T @ nf; ua = Ma.T @ nf
            if (ua == ub).all(): self.assertTrue(np.allclose(C, np.eye(2)))
            elif (ua == -ub).all(): self.assertTrue(np.allclose(C, -np.eye(2)))
            else: self.assertAlmostEqual(abs(np.trace(C)), 0.0)

    def test_mirror_image_is_gauge_equivalent(self):
        P = np.diag([-1, 1, 1])
        tilesP = [(P @ G @ P, P @ T, frozenset((-c[0]-1, c[1], c[2]) for c in cs)) for G, T, cs in self.tiles]
        ca = {k: v for k, v in plaquettes(self.tiles).items()}; cb = plaquettes(tilesP)
        tr = lambda c: collections.Counter({'2': c['+1'], '-2': c['-1'], '0': sum(v for k, v in c.items() if k not in ('+1', '-1'))})
        self.assertEqual(tr(ca), tr(cb))

class TestHierarchy(unittest.TestCase):
    def test_level2_counts_and_inheritance(self):
        t1, t2 = tiles_at_level(FR30, 1), tiles_at_level(FR30, 2)
        o2, e2 = panel_edges(t2); self.assertEqual((len(t2), len(e2), len(e2) - 64 + 1), (64, 576, 513))
        c1, c2 = plaquettes(t1), plaquettes(t2)
        N1, N2 = sum(c1.values()), sum(c2.values()); self.assertEqual((N1, N2), (60, 792))
        for k in (1, 2): self.assertEqual(18*8**k - 24*4**k + 6*2**k, (N1, N2)[k-1])
        cls = lambda c, s: sum(v for k, v in c.items() if k.strip('+-') == s) if s not in ('1', '-1') else c['+1' if s == '1' else '-1']
        for s in ('1', '-1', 'i', 'j', 'k'): self.assertGreaterEqual(cls(c2, s) - 8 * cls(c1, s), 0)
        self.assertEqual(c2['+1'] - 8 * c1['+1'], 177); self.assertEqual(c2['-1'] - 8 * c1['-1'], 18)
        links = [clifford_link(t2[a][0], t2[b][0], nf) for a, b, nf, _, _ in e2]
        self.assertEqual(len(generated_subgroup(fundamental_cycle_holonomies(64, e2, links))), 8)

    def test_random_decorations_never_flat(self):
        perms = list(itertools.permutations(range(3)))
        even = [p for p in perms if round(np.linalg.det(perm_mat(p))) == 1]; odd = [p for p in perms if round(np.linalg.det(perm_mat(p))) == -1]
        rng = np.random.default_rng(3)
        for _ in range(40):
            fr = {'0': even[rng.integers(3)]}
            for v in U3: fr[v] = (even if sum(v) % 2 == 0 else odd)[rng.integers(3)]
            t = tiles_at_level(fr, 1); o, e = panel_edges(t); links = [clifford_link(t[a][0], t[b][0], nf) for a, b, nf, _, _ in e]
            self.assertIn(len(generated_subgroup(fundamental_cycle_holonomies(8, e, links))), (4, 8))

class TestRefutedClaims(unittest.TestCase):
    def test_spin4_matrix_is_pairing_dependent(self):
        U4 = [v for v in itertools.product((0, 1), repeat=4) if v != (1, 1, 1, 1)]
        pk = sorted((u, mu, s) for u in U4 for mu in range(4) for s in (-1, 1) if tuple(u[i] + (s if i == mu else 0) for i in range(4)) not in U4)
        self.assertEqual(len(pk), 64)
        def build(mult, off):
            rows = []
            for idx in range(64):
                ua, mua, sa = pk[idx % 64]; ub, mub, sb = pk[(idx*mult + off) % 64]
                na = [0]*4; na[mua] = sa; nb = [0]*4; nb[mub] = sb; row = []
                for bidx, (mu, nu) in enumerate([(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]):
                    w = na[mu]*nb[nu] - na[nu]*nb[mu]
                    if w == 0 and idx % 6 == bidx: w = 1 if (idx//6) % 2 == 0 else -1
                    row.append(w)
                rows.append(row)
            return sp.Matrix(rows)
        self.assertEqual((build(7, 3).T * build(7, 3)).det(), 21414742)
        self.assertEqual(build(5, 1).rank(), 6); self.assertNotEqual((build(5, 1).T * build(5, 1)).det(), 21414742)

    def test_soldered_laplacian_gauge_artifact(self):
        tiles = tiles_at_level(FR30, 1); owner, edges = panel_edges(tiles); n = 8
        W = collections.Counter(); Np = collections.defaultdict(lambda: np.zeros((3, 3)))
        for a, b, nf, _, _ in edges: u, v = min(a, b), max(a, b); W[(u, v)] += 1; Np[(u, v)][int(np.argmax(nf)), int(np.argmax(nf))] += 1
        def assemble(cov):
            D = np.zeros((24, 24))
            for (u, v), w in W.items():
                Mu, Mv = tiles[u][0].astype(float), tiles[v][0].astype(float); N = Np[(u, v)]
                if cov: duu, dvv, off = Mu.T@(w*np.eye(3)+N)@Mu, Mv.T@(w*np.eye(3)+N)@Mv, -Mu.T@(w*np.eye(3)+N)@Mv
                else: duu, dvv, off = w*np.eye(3)+Mu.T@N@Mu, w*np.eye(3)+Mv.T@N@Mv, -(w*np.eye(3)+Mu.T@N@Mv)
                D[3*u:3*u+3, 3*u:3*u+3] += duu; D[3*v:3*v+3, 3*v:3*v+3] += dvv; D[3*u:3*u+3, 3*v:3*v+3] += off; D[3*v:3*v+3, 3*u:3*u+3] += off.T
            return D
        self.assertEqual(np.linalg.matrix_rank(assemble(False), tol=1e-9), 24)
        self.assertEqual(np.linalg.matrix_rank(assemble(True), tol=1e-9), 21)

if __name__ == "__main__":
    unittest.main()


class TestTypeSubstitutionRecursion(unittest.TestCase):
    """The finite type-substitution recursion derived from the inflation rule reproduces enumerated class counts."""
    def test_recursion_matches_enumeration_levels_1_to_3(self):
        import importlib.util, io, contextlib
        spec = importlib.util.spec_from_file_location("p4", os.path.join(ROOT, "audit", "phase4_type_substitution_proof.py"))
        # run the module up to the recursion (the SymPy spectral analysis is skipped here for speed)
        src = open(spec.origin).read().split("# ---------------- exact spectral analysis")[0]
        ns = {"__name__": "p4", "__file__": spec.origin}
        with contextlib.redirect_stdout(io.StringIO()):
            exec(compile(src, spec.origin, "exec"), ns)
        self.assertEqual((len(ns["ptypes_all"]), len(ns["qtypes_all"])), (49, 108))
        for m in (1, 2, 3):
            self.assertEqual({c: ns["rec"][m][c] for c in ns["CLASSES"]}, ns["measured"][m])
