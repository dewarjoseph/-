"""Phase V-B / Workstream A validation tests for the Phase V-A baseline objects.
Run from the repository root:  python3 -m unittest tests/test_phase5b_a_validation.py     (total < 3 min)
Everything is built by audit/phase5b_a_validation.py (own owner map, panel list, Pauli links, sparse assembly) on top of
the audited pose generator tiles_at_level of audit/independent_clifford_q8_audit.py."""
import os, sys, unittest, itertools, collections, time
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, os.path.join(os.path.dirname(HERE), 'audit'))
import phase5b_a_validation as V
from independent_clifford_q8_audit import FR30, tiles_at_level, panel_edges, clifford_link

I2 = np.eye(2, dtype=complex)
Q8 = [I2, -I2] + [s * 1j * V.SIG[k] for k in range(3) for s in (1, -1)]


def interior_tiles(tiles, owner):
    """Tiles none of whose cubes touches the patch surface (all 6 face-neighbours of all 7 cubes are in the patch)."""
    out = []
    for a, (_, _, cs) in enumerate(tiles):
        ok = True
        for c in cs:
            for ax in range(3):
                for s in (1, -1):
                    c2 = list(c); c2[ax] += s
                    if tuple(c2) not in owner: ok = False
        out.append(ok)
    return np.array(out)


def gauge_links(tiles, U):
    """Link table for the gauge-transformed connection C'_ab = U_a C_ab U_b^+."""
    base = V.link_table(tiles)
    def link(a, b, ax): return U[a] @ base(a, b, ax) @ U[b].conj().T
    return link


def random_su2(rng):
    q = rng.standard_normal(4); q /= np.linalg.norm(q)
    return q[0] * I2 + 1j * (q[1] * V.SIG[0] + q[2] * V.SIG[1] + q[3] * V.SIG[2])


class Base(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.L = {}
        for L in (1, 2, 3):
            tiles, owner, panels, link = V.build(L)
            Hp, deg = V.own_H(tiles, panels, pinned=True, link=link)
            Hf, _ = V.own_H(tiles, panels, pinned=False, link=link)
            cls.L[L] = dict(tiles=tiles, owner=owner, panels=panels, link=link, Hp=Hp, Hf=Hf, deg=deg)


class TestBoundaryConditions(Base):
    def test_interior_degree_24_and_boundary_below(self):
        for L in (2, 3):
            d = self.L[L]; inter = interior_tiles(d['tiles'], d['owner'])
            self.assertTrue(inter.any())
            self.assertTrue((d['deg'][inter] == 24).all())
            self.assertTrue((d['deg'][~inter] < 24).all())
            self.assertEqual(d['deg'].max(), 24)

    def test_pinned_minus_free_is_diagonal_on_boundary_tiles_only(self):
        for L in (1, 2, 3):
            d = self.L[L]; D = (d['Hp'] - d['Hf']).tocoo()
            self.assertTrue((D.row == D.col).all())
            tiles_hit = set((D.row[D.data != 0] // 2).tolist())
            boundary = set(np.nonzero(d['deg'] < 24)[0].tolist())
            self.assertEqual(tiles_hit, boundary)
            expected = np.repeat(24 - d['deg'], 2).astype(complex)
            self.assertTrue(np.array_equal(D.toarray().diagonal(), expected))

    def test_pinned_patch_is_exact_compression_of_next_level(self):
        """T_L is the (0,0,0)-child subtree of T_{L+1}: same poses as the first 8^L tiles and H_pin(T_L) equals the
        leading 2*8^L block of H_pin(T_{L+1}) entry by entry (compression theorem, Lemma 3.1 / Theorem 3.2)."""
        for L in (1, 2):
            small = self.L[L]; big = self.L[L + 1]; n = len(small['tiles'])
            for a in range(n):
                self.assertTrue((small['tiles'][a][0] == big['tiles'][a][0]).all())
                self.assertTrue((small['tiles'][a][1] == big['tiles'][a][1]).all())
                self.assertEqual(small['tiles'][a][2], big['tiles'][a][2])
            block = big['Hp'][:2 * n, :2 * n]
            diff = (block - small['Hp']).tocsr(); diff.eliminate_zeros()
            self.assertEqual(diff.nnz, 0)

    def test_bulk_formula_on_interior_rows(self):
        """On a tile with all 24 panels inside, the pinned row is 24 I - sum_f C_f, identical for the free operator."""
        d = self.L[3]; inter = np.nonzero(interior_tiles(d['tiles'], d['owner']))[0]
        Hp = d['Hp'].toarray(); Hf = d['Hf'].toarray()
        for a in inter[:50]:
            r = slice(2 * a, 2 * a + 2)
            self.assertTrue(np.array_equal(Hp[r], Hf[r]))
            self.assertTrue(np.array_equal(Hp[r, r], 24 * I2))
            # the off-diagonal row blocks are minus a sum of unitaries, one per panel: their squared Frobenius norm is 2 per panel
            offdiag = Hp[r].copy(); offdiag[:, r] = 0
            self.assertAlmostEqual(float((np.abs(offdiag) ** 2).sum()), 2 * 24, places=9)
            self.assertEqual(d['deg'][a], 24)


class TestGraphConstruction(Base):
    def test_counts_and_box_filling(self):
        for L in (1, 2, 3):
            d = self.L[L]; N = 2 ** (L + 1)
            self.assertEqual(len(d['tiles']), 8 ** L)
            self.assertEqual(len(d['owner']), 7 * 8 ** L)
            box = {c for c in itertools.product(range(N), repeat=3) if not all(x >= N // 2 for x in c)}
            self.assertEqual(set(d['owner']), box)
            self.assertEqual(len(d['panels']), 12 * (8 ** L - 4 ** L))

    def test_panel_multiset_symmetric(self):
        """Panels found from the lower cube looking +e_ax equal (as a multiset of (tile, tile, axis)) the panels found
        from the upper cube looking -e_ax with the roles swapped; and the undirected pair multiplicities are symmetric."""
        for L in (2, 3):
            d = self.L[L]; owner = d['owner']
            fwd = collections.Counter((a, b, ax) for a, b, ax, _ in d['panels'])
            bwd = collections.Counter()
            for c, b in owner.items():
                for ax in range(3):
                    c2 = list(c); c2[ax] -= 1; a = owner.get(tuple(c2))
                    if a is not None and a != b: bwd[(a, b, ax)] += 1
            self.assertEqual(fwd, bwd)
            und = collections.Counter()
            for a, b, ax, _ in d['panels']: und[(a, b)] += 1; und[(b, a)] += 1
            self.assertTrue(all(und[(a, b)] == und[(b, a)] for (a, b) in und))
            # multiset agrees with the audited panel_edges
            _, edges = panel_edges(d['tiles'])
            self.assertEqual(fwd, collections.Counter((a, b, int(np.argmax(nf))) for a, b, nf, _, _ in edges))

    def test_each_panel_in_four_edge_cycles_and_decomposition_identity(self):
        """Every unit face has 4 lattice edges; summing the 4-cycle forms h_e over ALL lattice edges touching the patch
        gives exactly 4 (D - A) = 4 H_free; over interior edges only, it equals 4 H_pin on tiles whose edges are all interior."""
        d = self.L[2]; tiles, owner, link = d['tiles'], d['owner'], d['link']; n = len(tiles)
        Hsum = np.zeros((2 * n, 2 * n), complex); Hint = np.zeros_like(Hsum)
        face_count = collections.Counter(); seen = set(); all_interior = np.ones(n, bool)
        for c in owner:
            for k in range(3):
                i, j = [x for x in range(3) if x != k]
                for di, dj in itertools.product((0, 1), repeat=2):
                    # lattice edge parallel to e_k through the corner c + di e_i + dj e_j; 4 cubes around it
                    base = list(c); base[i] += di; base[j] += dj; key = (k, tuple(base))
                    if key in seen: continue
                    seen.add(key)
                    cyc = []
                    for (si, sj) in ((0, 0), (1, 0), (1, 1), (0, 1)):
                        q = list(base); q[i] -= si; q[j] -= sj; cyc.append(tuple(q))
                    present = [q in owner for q in cyc]
                    he = np.zeros_like(Hsum)
                    for s in range(4):
                        q1, q2 = cyc[s], cyc[(s + 1) % 4]
                        if not (present[s] and present[(s + 1) % 4]): continue
                        t1, t2 = owner[q1], owner[q2]
                        if t1 == t2: continue
                        step = np.array(q2) - np.array(q1); ax = int(np.argmax(np.abs(step)))
                        C = link(t1, t2, ax) if step[ax] > 0 else link(t2, t1, ax).conj().T
                        face_count[(min(q1, q2), max(q1, q2))] += 1
                        he[2*t1:2*t1+2, 2*t1:2*t1+2] += I2; he[2*t2:2*t2+2, 2*t2:2*t2+2] += I2
                        he[2*t1:2*t1+2, 2*t2:2*t2+2] -= C; he[2*t2:2*t2+2, 2*t1:2*t1+2] -= C.conj().T
                    Hsum += he
                    if all(present): Hint += he
                    else:
                        for q in cyc:
                            if q in owner: all_interior[owner[q]] = False
        self.assertEqual(set(face_count.values()), {4})
        self.assertEqual(len(face_count), len(d['panels']))
        self.assertTrue(np.array_equal(Hsum, 4 * d['Hf'].toarray()))
        rows = np.repeat(all_interior, 2)
        self.assertTrue(rows.any())
        self.assertTrue(np.array_equal(Hint[rows], 4 * d['Hp'].toarray()[rows]))


class TestGaugeInvariance(Base):
    def test_q8_gauge(self):
        rng = np.random.default_rng(5)
        for L in (2, 3):
            d = self.L[L]; n = len(d['tiles']); U = [Q8[i] for i in rng.integers(0, 8, n)]
            link = gauge_links(d['tiles'], U); Hg, _ = V.own_H(d['tiles'], d['panels'], link=link)
            self.assertEqual(V.gaussian_integer_defect(Hg), 0.0)
            w0 = np.linalg.eigvalsh(d['Hp'].toarray()); w1 = np.linalg.eigvalsh(Hg.toarray())
            self.assertLess(np.abs(w0 - w1).max(), 1e-10)
            c0, _ = V.own_plaquettes(d['tiles'], d['owner'], True); c1, _ = V.own_plaquettes(d['tiles'], d['owner'], True, link=link)
            self.assertEqual(c0, c1)                       # all five Q8 conjugacy classes
            changed = sum(1 for a, b, ax, _ in d['panels'] if not np.allclose(link(a, b, ax), d['link'](a, b, ax)))
            self.assertGreater(changed, 0)                 # the gauge did change links

    def test_su2_gauge(self):
        rng = np.random.default_rng(7)
        for L in (2, 3):
            d = self.L[L]; n = len(d['tiles']); U = [random_su2(rng) for _ in range(n)]
            link = gauge_links(d['tiles'], U); Hg, _ = V.own_H(d['tiles'], d['panels'], link=link)
            self.assertLess(V.hermiticity_defect(Hg)[1], 1e-12)
            w0 = np.linalg.eigvalsh(d['Hp'].toarray()); w1 = np.linalg.eigvalsh(Hg.toarray())
            self.assertLess(np.abs(w0 - w1).max(), 1e-10)
            c0, _ = V.own_plaquettes(d['tiles'], d['owner'], True, classifier=V.classify_trace)
            c1, _ = V.own_plaquettes(d['tiles'], d['owner'], True, link=link, classifier=V.classify_trace)
            self.assertEqual(c0, c1)                       # trace classes {+1}, {-1}, traceless are SU(2)-invariant


class TestEigenvalueConvergence(Base):
    def test_dense_vs_lobpcg_level3(self):
        H = self.L[3]['Hp']
        lam_d, _, _ = V.solve_dense(H, 4)
        lam_l, _, res = V.solve_lobpcg(H, 4, block=8, seed=3, tol=1e-10, maxiter=3000)
        self.assertLess(np.abs(lam_d - lam_l).max(), 1e-8)
        self.assertLess(res.max(), 1e-7)

    def test_shift_invert_vs_lobpcg_level4(self):
        tiles, owner, panels, link = V.build(4); H, _ = V.own_H(tiles, panels, link=link)
        lam_s, _, res_s = V.solve_shift_invert(H, 4, sigma=8.0)
        lam_l, _, res_l = V.solve_lobpcg(H, 2, block=8, seed=3, tol=1e-9, maxiter=2500)
        self.assertLess(res_s.max(), 1e-10)
        self.assertLess(np.abs(lam_s[:2] - lam_l[:2]).max(), 1e-8)
        self.assertLess(abs(lam_s[1] - lam_s[0]), 1e-10)           # Kramers pair
        self.assertLess(abs(lam_s[0] - 8.919634360), 2e-9)         # certified rational Rayleigh quotient of Phase V-A, to its printed digits
        self.__class__.lam4 = lam_s[0]

    def test_pinned_bottoms_non_increasing(self):
        lows = [V.solve_dense(self.L[L]['Hp'], 2)[0][0] for L in (1, 2, 3)]
        lam4 = getattr(self.__class__, 'lam4', None)
        if lam4 is None:
            tiles, owner, panels, link = V.build(4); H, _ = V.own_H(tiles, panels, link=link); lam4 = V.solve_shift_invert(H, 2, sigma=8.0)[0][0]
        lows.append(lam4)
        for a, b in zip(lows, lows[1:]): self.assertLessEqual(b, a + 1e-12)
        self.assertLess(abs(lows[1] - 10.776950512), 1e-8); self.assertLess(abs(lows[2] - 9.378470210), 1e-8)


class TestNumericalPrecision(Base):
    def test_gaussian_integer_entries_and_exact_hermiticity(self):
        for L in (1, 2, 3):
            for key in ('Hp', 'Hf'):
                H = self.L[L][key]
                self.assertEqual(V.gaussian_integer_defect(H), 0.0)
                self.assertEqual(V.gaussian_integer_defect(4 * H), 0.0)
                nz, defect = V.hermiticity_defect(H)
                self.assertEqual((nz, defect), (0, 0.0))
                vals = set(np.round(H.data.real).astype(int).tolist()) | set(np.round(H.data.imag).astype(int).tolist())
                self.assertTrue(vals <= {-1, 0, 1} | set(range(0, 25)))

    def test_links_are_q8_and_match_audited_primitive(self):
        d = self.L[2]
        for a, b, ax, _ in d['panels']:
            C = d['link'](a, b, ax)
            self.assertTrue(any(np.allclose(C, q) for q in Q8))
            self.assertTrue(np.allclose(C, clifford_link(d['tiles'][a][0], d['tiles'][b][0], V.E3[ax])))
            self.assertTrue(np.allclose(V.pauli_link(d['tiles'][b][0], d['tiles'][a][0], V.E3[ax]), C.conj().T))   # C_ba = C_ab^+


if __name__ == '__main__':
    unittest.main()
