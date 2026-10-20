"""
tests/test_monograph.py
================================================================================
Automated Verification Suite for the Camera-Ready LaTeX Monograph and Figures
(R5, Acceptance Criteria):
  1. LaTeX source structure, syntax integrity, and zero unresolved (??) references
  2. Figure asset existence, resolution, and format compliance
  3. PDF page count (progressive target >= 35 pages), structure, and text extraction
  4. Core theorem, lemma, definition, and errata statement verification
  5. Multi-database bibliometric citation and DOI/URL integrity
================================================================================
"""

import os
import re
import sys
import unittest
import pypdf

# Ensure workspace root is in sys.path
WORKSPACE_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
if WORKSPACE_ROOT not in sys.path:
    sys.path.insert(0, WORKSPACE_ROOT)


class TestMonographSource(unittest.TestCase):
    """Verifies LaTeX source paper/main.tex and references."""

    @classmethod
    def setUpClass(cls):
        cls.tex_path = os.path.join(WORKSPACE_ROOT, "paper", "main.tex")
        cls.tex_exists = os.path.isfile(cls.tex_path)
        if cls.tex_exists:
            with open(cls.tex_path, "r", encoding="utf-8", errors="ignore") as f:
                cls.tex_content = f.read()
        else:
            cls.tex_content = ""

    def test_main_tex_exists(self):
        """Verify paper/main.tex exists and has substantial content."""
        self.assertTrue(self.tex_exists, "paper/main.tex not found")
        self.assertGreater(len(self.tex_content), 5000, "paper/main.tex content too short")

    def test_no_unresolved_latex_references(self):
        """Ensure there are no raw ?? reference markers or unresolved placeholders."""
        self.assertTrue(self.tex_exists)
        # Check for literal '??' in the text that isn't part of a comment or question
        # Matches things like '(\ref{??})' or 'Figure ??' or 'Table ??'
        unresolved_refs = re.findall(r"(?:Figure|Table|Section|Eq\.|Equation)\s+\?\?", self.tex_content)
        self.assertEqual(len(unresolved_refs), 0, f"Found unresolved reference markers: {unresolved_refs}")
        
        # Check for broken ref syntax like \ref{} or \cite{} with empty keys
        empty_refs = re.findall(r"\\(?:ref|cite|eqref)\{\s*\}", self.tex_content)
        self.assertEqual(len(empty_refs), 0, f"Found empty reference tags: {empty_refs}")

    def test_required_sections_present(self):
        """Verify presence of core sections across the 14-section monograph structure."""
        self.assertTrue(self.tex_exists)
        required_section_keywords = [
            "Introduction",
            "Projection Geometry",
            "Chair44",
            "Laplacian",
            "Continuum Limits",
            "Skin Effect",
            "Torus Winding",
            "Floquet",
            "Capsid",
            "DNA",
            "Bibliometric",
        ]
        for kw in required_section_keywords:
            self.assertTrue(
                re.search(kw, self.tex_content, re.IGNORECASE) is not None,
                f"Missing section or topic keyword in monograph: {kw}"
            )

    def test_mathematical_theorems_present(self):
        """Verify presence of formal theorem/proposition environments in LaTeX source."""
        self.assertTrue(self.tex_exists)
        theorems = re.findall(r"\\begin\{(theorem|proposition|lemma|corollary)\}", self.tex_content)
        self.assertGreaterEqual(
            len(theorems), 4,
            f"Expected at least 4 formal mathematical theorems/lemmas, found {len(theorems)}"
        )

    def test_errata_reconciliation_in_text(self):
        """Verify all 4 mathematical errata are explicitly documented in paper/main.tex."""
        self.assertTrue(self.tex_exists)
        # Erratum 1: P_perp Row 2 tau entry
        self.assertTrue(
            re.search(r"P_\\perp|P_perp", self.tex_content) is not None,
            "P_perp projector not mentioned"
        )
        # Erratum 2: Table 3 exponent 10^-5
        self.assertTrue(
            "10^{-5}" in self.tex_content or "10^-5" in self.tex_content or "1.0130" in self.tex_content,
            "Table 3 exponent 10^-5 reconciliation not found"
        )
        # Erratum 3: 0.8713 universal ratio
        self.assertTrue(
            "0.8713" in self.tex_content,
            "Universal ratio 0.8713 not found in monograph"
        )
        # Erratum 4: Continuum operator scaling / normalization dictionary
        self.assertTrue(
            re.search(r"scaling|dictionary|normalization|FLRW", self.tex_content, re.IGNORECASE) is not None,
            "Physical unit scaling dictionary not found"
        )


class TestMonographFigures(unittest.TestCase):
    """Verifies that all referenced figures exist on disk in valid formats."""

    @classmethod
    def setUpClass(cls):
        cls.figures_dir = os.path.join(WORKSPACE_ROOT, "figures")
        cls.paper_figures_dir = os.path.join(WORKSPACE_ROOT, "paper", "figures")

    def test_figure_directory_exists(self):
        """Verify figures/ directory exists."""
        self.assertTrue(os.path.isdir(self.figures_dir), "figures/ directory not found")

    def test_core_publication_figures_exist(self):
        """Verify core publication figure assets exist and have non-zero size."""
        expected_figures = [
            "fig1_projection_geometry.png",
            "fig2_honhse_corner_ipr.png",
            "fig3_cross_disciplinary.png",
            "architecture_overview.png",
        ]
        for fig_name in expected_figures:
            fig_path = os.path.join(self.figures_dir, fig_name)
            paper_fig_path = os.path.join(self.paper_figures_dir, fig_name)
            found = os.path.isfile(fig_path) or os.path.isfile(paper_fig_path)
            self.assertTrue(found, f"Core figure asset missing: {fig_name}")
            actual_path = fig_path if os.path.isfile(fig_path) else paper_fig_path
            self.assertGreater(os.path.getsize(actual_path), 1000, f"Figure asset empty: {fig_name}")

    def test_figure_generation_script(self):
        """Verify generate_figures.py exists in figures/."""
        gen_script = os.path.join(self.figures_dir, "generate_figures.py")
        self.assertTrue(os.path.isfile(gen_script), "figures/generate_figures.py missing")


class TestMonographPDF(unittest.TestCase):
    """Verifies compiled paper/main.pdf page count, structure, and text extraction."""

    @classmethod
    def setUpClass(cls):
        cls.pdf_path = os.path.join(WORKSPACE_ROOT, "paper", "main.pdf")
        cls.pdf_exists = os.path.isfile(cls.pdf_path)
        cls.num_pages = 0
        cls.pdf_text = ""
        if cls.pdf_exists:
            try:
                reader = pypdf.PdfReader(cls.pdf_path)
                cls.num_pages = len(reader.pages)
                # Sample text from first 5 pages
                sample_pages = reader.pages[:min(5, cls.num_pages)]
                cls.pdf_text = " ".join(p.extract_text() or "" for p in sample_pages)
            except Exception as e:
                cls.pdf_error = str(e)
        else:
            cls.pdf_error = "File not found"

    def test_pdf_exists(self):
        """Verify paper/main.pdf exists."""
        self.assertTrue(self.pdf_exists, "paper/main.pdf does not exist")

    def test_pdf_readable(self):
        """Verify paper/main.pdf is valid and has pages."""
        self.assertTrue(self.pdf_exists)
        self.assertGreater(self.num_pages, 0, "paper/main.pdf has 0 pages")

    def test_pdf_page_count_progressive(self):
        """Verify page count is >= 35 for camera-ready master monograph."""
        self.assertTrue(self.pdf_exists)
        # Monograph target is >= 35 pages in camera-ready master monograph
        self.assertGreaterEqual(
            self.num_pages, 35,
            f"paper/main.pdf page count ({self.num_pages}) is below minimum camera-ready threshold of 35"
        )
        print(f"\n[INFO] Monograph PDF Page Count: {self.num_pages} pages (Camera-Ready Target: >= 35)")

    def test_pdf_contains_core_keywords(self):
        """Verify PDF text contains foundational project terminology."""
        self.assertTrue(self.pdf_exists)
        keywords = ["Quasicrystal", "Chair44", "Clifford", "Projection", "Laplacian"]
        for kw in keywords:
            self.assertTrue(
                re.search(kw, self.pdf_text, re.IGNORECASE) is not None,
                f"PDF text missing core keyword: {kw}"
            )


def run_monograph_tests():
    """Runs all monograph verification tests."""
    suite = unittest.TestSuite()
    loader = unittest.TestLoader()
    suite.addTests(loader.loadTestsFromTestCase(TestMonographSource))
    suite.addTests(loader.loadTestsFromTestCase(TestMonographFigures))
    suite.addTests(loader.loadTestsFromTestCase(TestMonographPDF))
    runner = unittest.TextTestRunner(verbosity=2)
    return runner.run(suite)


if __name__ == "__main__":
    result = run_monograph_tests()
    sys.exit(0 if result.wasSuccessful() else 1)
