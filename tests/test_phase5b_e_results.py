"""
Regression tests for Phase 5B / Workstream E (files under audit/results/phase5b_e_*).  They check the recorded
certificates for internal consistency (exact rationals, bracket ordering, the consistency flags written by the scripts)
and the saved level-6 ground vector; they do not rebuild the level-6 operator (1 GB, minutes).
Run:  python3 -m unittest tests/test_phase5b_e_results.py
"""
import os, re, unittest
from fractions import Fraction
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__)); RES = os.path.join(os.path.dirname(HERE), 'audit', 'results')
def read(name):
    with open(os.path.join(RES, name)) as f: return f.read()

class TestPhase5bE(unittest.TestCase):
    def test_bracket(self):
        up = read('phase5b_e_level6_certificate.txt'); lo = read('phase5b_e_radius2_bound.txt')
        m = re.search(r"E_bulk <= lambda_min\(H\^pin_6\) <= (\d+)/(\d+)", up); self.assertIsNotNone(m)
        q6 = Fraction(int(m.group(1)), int(m.group(2)))
        m = re.search(r"CERTIFIED: E_bulk >= .* = (\d+)/(\d+) = ", lo); self.assertIsNotNone(m)
        lb = Fraction(int(m.group(1)), int(m.group(2)))
        self.assertEqual(lb, Fraction(72147403, 18000000))
        self.assertLess(lb, q6)
        self.assertLess(q6, Fraction(87702, 10000))                      # target E_bulk <= 8.7702
        self.assertGreater(q6, Fraction(87701, 10000))                   # consistent with the LOBPCG value 8.7701336
        self.assertLess(q6, Fraction(2476138622922986, 281474983842677)) # improves the level-5 certificate
        self.assertIn("(A) == (B) bit for bit: True", up)
    def test_level6_vector(self):
        v = np.load(os.path.join(RES, 'phase5b_e_fr30_level6_groundstate.npy'))
        self.assertEqual(v.shape, (524288,)); self.assertEqual(v.dtype, np.complex128)
        self.assertAlmostEqual(float(np.linalg.norm(v)), 1.0, places=9)
    def test_radius2_census_and_certificates(self):
        lo = read('phase5b_e_radius2_bound.txt')
        self.assertIn("V_2 := Phi_2(V_1): 165 two-star types", lo)
        for m in (5, 6, 7): self.assertRegex(lo, rf"T_{m}: .*distinct types 165; subset of V_2: True; equal to V_2: True; missing 0")
        self.assertIn("Phi_22(V_2) subset V_2: True", lo)
        self.assertRegex(lo, r"exact certificates: 162 signatures, 162 non-flat certified .*, 0 failures")
        self.assertRegex(lo, r"rejects mu_c \+ 1e-5 for (\d+) of \1 sampled")
        self.assertIn("= 0.0e+00", lo)   # 1/18 identity exact on T_3
    def test_recursion_correlations(self):
        r = read('phase5b_e_recursion_correlations.txt')
        for m in (2, 3, 4): self.assertIn(f"exact recursion v_{m} = 8^{m-1} f + sum S v_{m-1} verified coordinate-wise for all five shapes: True", r)
        self.assertIn("-> agreement: True", r)                         # Theorem A class frequencies re-derived
        self.assertIn("charpoly(Phi) = lambda**70*(lambda - 8)*(lambda - 1)", r)
        self.assertIn("nullity of Phi - 8: 1 (simple eigenvalue 8: True)", r)
        self.assertIn("equals 18 x Theorem A frequencies (19/2, 13/8, 2, 23/8, 2): True", r)
        self.assertIn("must equal the all-edge marginal (18 pq + 3 delta_1)/21: True", r)
        self.assertIn("2 x (13/8) / 7 = 13/28: True", r)
        self.assertIn("mean 11/2", r)
    def test_moments(self):
        t = read('phase5b_e_ids_moments.txt')
        self.assertIn("m_0 = 2, m_1 = 48, m_2 = 1296, m_3 = 37908, m_4 = 1169988", t)
        self.assertIn("m_2 (1-stars) == m_2 (3-stars): True; m_3 (1-stars) == m_3 (3-stars): True", t)
        self.assertIn("445 types", t)
if __name__ == '__main__':
    unittest.main()
