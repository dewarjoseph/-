"""
Phase V-A, Task A5: the Lean template audit/lean_template_type_substitution.lean carries a data-independent general
closed-form theorem (closed_form_general) and finite Q8 class-invariance theorems; the generated certificate
certificates/TypeSubstitutionCertificate.lean must be exactly the template with the data block substituted.
These tests are text-level consistency checks (no Lean binary needed).  Set PHASE5A_LEAN=/path/to/lean to additionally
compile a data-free extract of the new theorems with the Lean kernel (fast, a few seconds; no native_decide anywhere).
"""
import os, re, subprocess, tempfile, unittest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
TEMPLATE = os.path.join(ROOT, "audit", "lean_template_type_substitution.lean")
CERT = os.path.join(ROOT, "certificates", "TypeSubstitutionCertificate.lean")

NEW_THEOREMS = ("closed_form_general", "step_case_general", "applyG_add", "applyG_smul", "applyG_congr",
                "closed_form_all_direct", "applyS_eq_applyG", "CF_eq_CFG",
                "q8_closed", "q8_conj_is_inverse", "q8_class_conj_invariant", "q8_class_inverse_invariant")
OLD_THEOREMS = ("types_distinct", "panel_images_certified", "plaquette_images_certified", "classes_certified",
                "standard_level1_certified", "equivariance_certified", "seed_certified",
                "level1_geometry_matches_recursion", "level2_geometry_matches_recursion", "eigen_check", "u1_check",
                "u2_check", "base_check", "foldl_add_split", "foldl_smul", "foldl_congr_mem", "applyS_add", "applyS_smul",
                "applyS_congr", "eigen_identities", "useq1_eq", "useq2_eq", "base_case", "step_case", "closed_form_all",
                "wsum_add", "wsum_smul", "wsum_congr", "wsum_closed_form", "class_counts_closed_form",
                "total_closed_form", "limit_frequencies")


def strip_data(cert_text):
    """Undo the exporter's substitution: cut the data block back to the '-- <<DATA>>' marker."""
    i = cert_text.index("\n/-! ## Certificate data")
    j = cert_text.index("def U2L : List Int := ")
    j = cert_text.index("\n", j) + 1
    return cert_text[:i] + "-- <<DATA>>" + cert_text[j:]


class TestPhase5ALeanGeneralTheorem(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tmpl = open(TEMPLATE).read()
        cls.cert = open(CERT).read()

    def test_new_and_old_theorems_present_in_template_and_certificate(self):
        for s in (self.tmpl, self.cert):
            for name in NEW_THEOREMS + OLD_THEOREMS:
                self.assertRegex(s, rf"(?m)^theorem {name}\b", msg=name)

    def test_general_theorem_statement_is_the_specified_one(self):
        stmt = ("theorem closed_form_general (N : Nat) (S : Nat → Nat → Int) (f W8 W4 W2 W1 : Nat → Int) (D : Int)\n"
                "    (u : Nat → Nat → Int) (hu0 : ∀ r, u 0 r = f r)\n"
                "    (hu : ∀ j r, u (j+1) r = applyG N S (u j) r + (8:Int)^(j+1) * f r)\n"
                "    (h8 : ∀ r, r < N → applyG N S W8 r + D * f r = 8 * W8 r) (h4 : ∀ r, r < N → applyG N S W4 r = 4 * W4 r)\n"
                "    (h2 : ∀ r, r < N → applyG N S W2 r = 2 * W2 r) (h1 : ∀ r, r < N → applyG N S W1 r = W1 r)\n"
                "    (hbase : ∀ r, r < N → D * u 2 r = CFG W8 W4 W2 W1 2 r) :\n"
                "    ∀ j, 2 ≤ j → ∀ r, r < N → D * u j r = CFG W8 W4 W2 W1 j r := by")
        self.assertIn(stmt, self.tmpl)
        self.assertIn("def applyG (N : Nat) (S : Nat → Nat → Int) (x : Nat → Int) (r : Nat) : Int :=\n"
                      "  (List.range N).foldl (fun acc c => acc + S r c * x c) 0", self.tmpl)
        # the concrete theorem keeps its name and statement and is derived by instantiation
        self.assertIn("theorem closed_form_all : ∀ j, 2 ≤ j → closedFormHolds j :=\n"
                      "  closed_form_general N Sentry fvec W8 W4 W2 W1 D useq", self.tmpl)

    def test_q8_theorems_are_finite_decide_checks(self):
        self.assertIn("theorem q8_class_conj_invariant :\n    ∀ g ∈ q8Elements, ∀ w ∈ q8Elements, "
                      "classOfQ (qmul (qmul g w) (qconj g)) = classOfQ w := by decide", self.tmpl)
        self.assertIn("theorem q8_class_inverse_invariant : ∀ w ∈ q8Elements, classOfQ (qconj w) = classOfQ w := by decide",
                      self.tmpl)
        self.assertIn("def qconj (a : Q) : Q := ⟨a.s, -a.x, -a.y, -a.z⟩", self.tmpl)
        elems = re.search(r"def q8Elements : List Q :=\n  \[(.*?)\]", self.tmpl).group(1)
        self.assertEqual(elems.count("⟨"), 8)

    def test_no_sorry_axiom_or_native_decide(self):
        for s in (self.tmpl, self.cert):
            self.assertNotIn("sorry", s)
            self.assertNotIn("native_decide", s)
            self.assertIsNone(re.search(r"^\s*axiom\b", s, re.M))
        self.assertEqual(self.cert.count("decide +kernel"), 14)

    def test_certificate_is_template_plus_data(self):
        """The generated certificate equals the template with the data block and the three size placeholders filled."""
        back = strip_data(self.cert)
        expect = self.tmpl.replace("<<NP>>", "49").replace("<<NQ>>", "108").replace("<<N>>", "157")
        self.assertEqual(back, expect)
        self.assertIn("def D : Int := 64", self.cert)

    def test_print_axioms_lines_for_new_theorems(self):
        for name in ("closed_form_general", "closed_form_all_direct", "q8_closed", "q8_conj_is_inverse",
                     "q8_class_conj_invariant", "q8_class_inverse_invariant", "closed_form_all"):
            self.assertIn(f"#print axioms TypeSubstitution.{name}\n", self.cert)

    def test_datafree_extract_compiles_with_kernel(self):
        """Optional: compile prelude + fold lemmas + general section (no certificate data) with the Lean kernel."""
        lean = os.environ.get("PHASE5A_LEAN")
        if not lean or not os.path.exists(lean):
            self.skipTest("set PHASE5A_LEAN=/path/to/lean to run")
        t = self.tmpl
        A = t[:t.index("-- <<DATA>>")]
        B = t[t.index("/-! ### Elementary fold lemmas"):t.index("theorem applyS_add (x y : Nat → Int) (r : Nat) :")]
        src = A + B + "\nend TypeSubstitution\n#print axioms TypeSubstitution.closed_form_general\n" \
              "#print axioms TypeSubstitution.q8_class_conj_invariant\n#print axioms TypeSubstitution.q8_class_inverse_invariant\n"
        with tempfile.TemporaryDirectory() as d:
            p = os.path.join(d, "DataFree.lean"); open(p, "w").write(src)
            r = subprocess.run([lean, p], capture_output=True, text=True, timeout=600)
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        self.assertNotIn("error", r.stdout + r.stderr)
        self.assertIn("'TypeSubstitution.closed_form_general' depends on axioms: [propext, Quot.sound]", r.stdout)
        self.assertIn("'TypeSubstitution.q8_class_conj_invariant' does not depend on any axioms", r.stdout)
        self.assertIn("'TypeSubstitution.q8_class_inverse_invariant' does not depend on any axioms", r.stdout)


if __name__ == "__main__":
    unittest.main()
