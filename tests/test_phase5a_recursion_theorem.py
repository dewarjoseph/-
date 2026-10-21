"""
Tests for audit/phase5a_recursion_theorem_audit.py and audit/phase5a_counterexamples.py (fast: no geometry
enumeration; the operator is rebuilt from the index lists of certificates/TypeSubstitutionCertificate.lean, and the
clean-spectrum criterion is exercised on hand-built matrices whose spectra are known in closed form).
Run:  python3 -m unittest tests/test_phase5a_recursion_theorem.py
"""
import os, sys, io, unittest, importlib.util, contextlib
import sympy as sp

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
def _load(name):
    spec = importlib.util.spec_from_file_location(name, os.path.join(ROOT, "audit", name + ".py"))
    mod = importlib.util.module_from_spec(spec); spec.loader.exec_module(mod); return mod
R = _load("phase5a_recursion_theorem_audit")
CX = _load("phase5a_counterexamples")
lam = R.lam

def quiet(fn, *a, **k):
    with contextlib.redirect_stdout(io.StringIO()):
        return fn(*a, **k)


class TestCertificateOperator(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.cert = R.parse_lean_lists()
        cls.S, cls.f, cls.nP, cls.nQ = R.S_from_certificate(cls.cert)
        cls.N = cls.nP + cls.nQ
        cls.M = cls.S[:cls.nP, :cls.nP]; cls.B = cls.S[cls.nP:, cls.nP:]; cls.A = cls.S[cls.nP:, :cls.nP]

    def test_sizes_and_column_sums(self):
        self.assertEqual((self.nP, self.nQ, self.N), (49, 108, 157))
        self.assertEqual(set(R.colsums(self.M)), {4}); self.assertEqual(set(R.colsums(self.A)), {4}); self.assertEqual(set(R.colsums(self.B)), {2})
        self.assertTrue(self.S[:self.nP, self.nP:].is_zero_matrix)
        self.assertEqual((sum(self.f[:self.nP]), sum(self.f[self.nP:])), (48, 60))
        self.assertGreater(len(set(R.rowsums(self.M))), 1)   # row sums are not constant

    def test_characteristic_polynomials(self):
        cpM, cpB, cpS = R.charpoly_expr(self.M), R.charpoly_expr(self.B), R.charpoly_expr(self.S)
        self.assertEqual(sp.expand(cpM - lam**44 * (lam - 4) * (lam - 1)**4), 0)
        self.assertEqual(sp.expand(cpB - lam**103 * (lam - 2) * (lam - 1)**4), 0)
        self.assertEqual(sp.expand(cpS - cpM * cpB), 0)

    def test_semisimple_and_nilpotency_index(self):
        I = sp.eye(self.N)
        for ev, alg in ((4, 1), (2, 1), (1, 8)):
            r1 = R.rank_exact(self.S - ev * I); r2 = R.rank_exact((self.S - ev * I)**2)
            self.assertEqual(self.N - r1, alg); self.assertEqual(r1, r2)
        r1, r2, r3 = R.rank_exact(self.S), R.rank_exact(self.S**2), R.rank_exact(self.S**3)
        self.assertGreater(r1, r2); self.assertEqual(r2, r3); self.assertEqual(self.N - r2, 147)

    def test_closed_form_from_certificate_vectors(self):
        c = self.cert; D = c['D']; self.assertEqual(D, 64)
        W = {8: c['W8L'], 4: c['W4L'], 2: c['W2L'], 1: c['W1L']}
        v = R.recursion_vectors(self.S, self.f, 9)
        for m in range(2, 10):      # holds from m = 2 = nilpotency index of the 0-part (Lean proves m >= 3)
            self.assertTrue(all(D * v[m][i] == 8**m * W[8][i] + 4**m * W[4][i] + 2**m * W[2][i] + W[1][i] for i in range(self.N)), m)
        self.assertFalse(all(D * v[1][i] == 8 * W[8][i] + 4 * W[4][i] + 2 * W[2][i] + W[1][i] for i in range(self.N)))
        SW = {k: sp.Matrix(W[k]) for k in W}
        self.assertEqual(self.S * SW[8] + D * self.f, 8 * SW[8]); self.assertEqual(self.S * SW[4], 4 * SW[4])
        self.assertEqual(self.S * SW[2], 2 * SW[2]); self.assertEqual(self.S * SW[1], SW[1])
        # W8 recomputed from (8 - S)^{-1} f
        W8r = (8 * sp.eye(self.N) - self.S).LUsolve(self.f)
        self.assertEqual([int(D * x) for x in W8r], W[8])
        tot = sum(W[8][self.nP:]); self.assertEqual(sp.Rational(tot, D), 18)
        cls = c['plaqClassCert']
        freqs = [sp.Rational(sum(W[8][self.nP + q] for q in range(self.nQ) if cls[q] == ci), tot) for ci in range(5)]
        self.assertEqual(freqs, [sp.Rational(19, 36), sp.Rational(13, 144), sp.Rational(1, 9), sp.Rational(23, 144), sp.Rational(1, 9)])

    def test_fr30_condensation_is_clean(self):
        resM = quiet(R.analyse_blocks, self.M, 4, 'M', list_types=False)
        resB = quiet(R.analyse_blocks, self.B, 2, 'B', list_types=False)
        for res, K in ((resM, 4), (resB, 2)):
            self.assertTrue(res['clean']); self.assertTrue(res['clean_blocks']); self.assertTrue(res['clause_i']); self.assertTrue(res['clause_ii'])
            self.assertTrue(res['pred_ok']); self.assertTrue(res['sink_simple']); self.assertEqual(res['multK'], res['n_sink'])
            self.assertEqual(res['nonclean'], {})
        self.assertEqual(resM['n_sink'], 1); self.assertEqual(resB['n_sink'], 1)
        # M: no self-reproducing singleton (no M[c,c] = 4); the unique sink is a 7-type irreducible block of rank 2 with
        # charpoly lambda^5 (lambda-4)(lambda-1); three loop-1 singletons supply the other three eigenvalues 1
        self.assertEqual([i for i in range(49) if self.M[i, i] == 4], [])
        sinkM = [r for r in resM['rows'] if r['sink']][0]
        self.assertEqual(sinkM['nodes'], [0, 2, 5, 9, 14, 25, 42]); self.assertEqual((sinkM['rank'], sinkM['trace']), (2, 5))
        self.assertEqual(sp.expand(sinkM['cp'] - lam**5 * (lam - 4) * (lam - 1)), 0)
        self.assertEqual(sum(1 for r in resM['rows'] if r['kind'].startswith('fixed-point')), 3)
        self.assertEqual(sum(1 for r in resM['rows'] if r['kind'].startswith('transient')), 39)
        # B: the unique sink is the rank-1 block [[1,1],[1,1]] on types {1, 49}; four loop-1 singletons
        sinkB = [r for r in resB['rows'] if r['sink']][0]
        self.assertEqual(sinkB['nodes'], [1, 49]); self.assertEqual(self.B.extract([1, 49], [1, 49]), sp.Matrix([[1, 1], [1, 1]]))
        self.assertEqual(sum(1 for r in resB['rows'] if r['kind'].startswith('fixed-point')), 4)
        self.assertEqual(sum(1 for r in resB['rows'] if r['kind'].startswith('transient')), 102)
        self.assertTrue(resM['rank_pred_ok'] and resB['rank_pred_ok'])


class TestCriterionOnSyntheticMatrices(unittest.TestCase):
    def run_blocks(self, Mat, K):
        return quiet(R.analyse_blocks, sp.Matrix(Mat), K, 'synthetic', list_types=False)

    def test_singleton_with_loop_2_is_the_only_defect(self):
        # node 0: 2 copies of itself + 2 of node 1; node 1: self-reproducing sink.  spectrum {2, 4}: not clean, not a cycle, not a block
        res = self.run_blocks([[2, 0], [2, 4]], 4)
        self.assertFalse(res['clean']); self.assertFalse(res['clause_i']); self.assertTrue(res['clause_ii'])
        self.assertEqual(res['n_sink'], 1); self.assertEqual(res['multK'], 1); self.assertTrue(res['pred_ok'])
        self.assertEqual(list(res['nonclean']), ['lambda - 2'])
        self.assertIn('NON-CLEAN singleton with loop 2', res['nonclean']['lambda - 2'][0])

    def test_three_cycle_gives_primitive_cube_roots(self):
        # 0 -> 1 -> 2 -> 0 with weight 1, 3 copies each to the sink node 3 (loop 4)
        Mat = [[0, 0, 1, 0], [1, 0, 0, 0], [0, 1, 0, 0], [3, 3, 3, 4]]
        res = self.run_blocks(Mat, 4)
        self.assertFalse(res['clean']); self.assertTrue(res['pred_ok'])
        cyc = [r for r in res['rows'] if r['k'] == 3][0]
        self.assertTrue(cyc['kind'].startswith('cycle of length 3')); self.assertFalse(cyc['sink'])
        self.assertEqual(sp.expand(cyc['cp'] - (lam**3 - 1)), 0)
        self.assertIn('lambda**2 + lambda + 1', res['nonclean'])

    def test_sink_blocks_of_size_two(self):
        clean_sink = self.run_blocks([[2, 2], [2, 2]], 4)       # eigenvalues 4, 0 -> clean although the sink is not a single node
        self.assertTrue(clean_sink['clean']); self.assertTrue(clean_sink['clause_ii']); self.assertEqual(clean_sink['n_sink'], 1)
        self.assertEqual(clean_sink['rows'][0]['kind'], 'irreducible SINK block of size 2'); self.assertEqual(clean_sink['rows'][0]['rank'], 1)
        rank2 = self.run_blocks([[3, 2], [1, 2]], 4)             # rank 2, trace 5 = K+1 -> eigenvalues 4, 1: clean
        self.assertTrue(rank2['clean']); self.assertTrue(rank2['rank_pred_ok']); self.assertEqual(rank2['rows'][0]['trace'], 5)
        bad_sink = self.run_blocks([[3, 1], [1, 3]], 4)         # rank 2, trace 6 = K+2 -> eigenvalues 4, 2: clause (ii) fails
        self.assertFalse(bad_sink['clean']); self.assertFalse(bad_sink['clause_ii']); self.assertTrue(bad_sink['clause_i']); self.assertTrue(bad_sink['rank_pred_ok'])
        imprim = self.run_blocks([[0, 4], [4, 0]], 4)           # period 2: eigenvalues 4, -4
        self.assertFalse(imprim['clean']); self.assertFalse(imprim['clause_ii']); self.assertEqual(imprim['multK'], 1)

    def test_non_sink_irreducible_block_is_never_clean(self):
        # nodes 0,1 feed each other (col sums 3 within the block) and send 1 copy each to the sink 2
        Mat = [[1, 2, 0], [2, 1, 0], [1, 1, 4]]
        res = self.run_blocks(Mat, 4)
        blk = [r for r in res['rows'] if r['k'] == 2][0]
        self.assertFalse(blk['sink']); self.assertFalse(blk['clean']); self.assertIs(blk['pred'], False)
        self.assertEqual(sp.expand(blk['cp'] - (lam - 3) * (lam + 1)), 0)
        self.assertEqual(res['multK'], res['n_sink'], 1)

    def test_multiplicity_of_K_counts_sinks(self):
        Mat = [[4, 0, 1], [0, 4, 1], [0, 0, 2]]   # two self-reproducing sinks, one singleton with loop 2
        res = self.run_blocks(Mat, 4)
        self.assertEqual(res['n_sink'], 2); self.assertEqual(res['multK'], 2); self.assertFalse(res['clean'])

    def test_root_mult_and_is_clean(self):
        self.assertEqual(R.root_mult((lam - 4)**2 * lam * (lam - 1), 4), 2)
        self.assertEqual(R.root_mult(lam**3 * (lam - 1), 4), 0)
        self.assertTrue(R.is_clean(lam**5 * (lam - 1)**2 * (lam - 4), (1, 4)))
        self.assertFalse(R.is_clean(lam * (lam - 2) * (lam - 4), (1, 4)))


class TestCounterexamples(unittest.TestCase):
    def test_fibonacci_irrational(self):
        r = quiet(CX.example_a, io.StringIO())
        self.assertEqual(sp.expand(r['cp'] - (lam**2 - lam - 1)), 0); self.assertTrue(r['irrational']); self.assertTrue(r['rec_ok'])
        phi = (1 + sp.sqrt(5)) / 2
        self.assertEqual(sp.simplify(r['u'][0] - 1 / phi), 0); self.assertEqual(sp.simplify(r['u'][1] - 1 / phi**2), 0)

    def test_non_primitive_seed_dependence_and_forced_contrast(self):
        r = quiet(CX.example_b, io.StringIO())
        self.assertTrue(r['seed_dependent']); self.assertFalse(r['primitive']); self.assertTrue(r['ratio_ok'])
        self.assertEqual(r['forced_limit'], [sp.Rational(1, 6), sp.Rational(1, 3)])

    def test_thue_morse_two_block_spectrum(self):
        r = quiet(CX.example_c, io.StringIO())
        self.assertTrue(r['clean1']); self.assertFalse(r['clean2'])
        self.assertEqual(sp.expand(r['cp2'] - lam * (lam - 2) * (lam - 1) * (lam + 1)), 0)
        self.assertEqual(r['alph2'], ['00', '01', '10', '11'])
        self.assertEqual(r['u2'], [sp.Rational(1, 6), sp.Rational(1, 3), sp.Rational(1, 3), sp.Rational(1, 6)])
        M2 = sp.Matrix(r['Mat2']); self.assertEqual(set(R.colsums(M2)), {2})

    def test_period_doubling(self):
        r = quiet(CX.example_d, io.StringIO())
        self.assertFalse(r['clean']); self.assertTrue(r['cf_ok'])
        self.assertEqual(sp.expand(r['cp'] - (lam - 2) * (lam + 1)), 0)
        self.assertEqual(r['u'], [sp.Rational(2, 3), sp.Rational(1, 3)])


if __name__ == '__main__':
    unittest.main()
