"""Regression checks for silent research-artifact drift."""

from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
from check_repository import check_links, check_manifest, check_sources, check_tex_log


class RepositoryChecks(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        self.paper = self.root / "main.tex"
        self.manifest = self.root / "FORMALIZATION.md"
        self.paper.write_text(r"\begin{theorem}\label{thm:one}Claim.\end{theorem}")
        self.manifest.write_text("| `thm:one` | Claim | checked | `provedOne` |\n")

    def test_new_theorem_requires_coverage(self):
        self.assertEqual(check_manifest(self.root)[0], [])
        with self.paper.open("a") as output:
            output.write(r"\begin{lemma}\label{lem:two}Claim.\end{lemma}")
        self.assertIn("Missing manifest row: lem:two", check_manifest(self.root)[0])

    def test_commented_results_are_ignored(self):
        with self.paper.open("a") as output:
            output.write("\n% " + r"\begin{lemma}\label{lem:old}\end{lemma}" + "\n")
        self.assertEqual(check_manifest(self.root)[0], [])

    def test_unlabelled_result_is_rejected(self):
        self.paper.write_text(r"\begin{theorem}Claim.\end{theorem}")
        self.assertTrue(any("primary theorem label" in error for error in check_manifest(self.root)[0]))

    def test_duplicate_and_stale_rows_are_rejected(self):
        with self.manifest.open("a") as output:
            output.write("| `thm:one` | Claim | checked | `provedOne` |\n")
            output.write("| `lem:old` | Removed | open | Missing |\n")
        errors = check_manifest(self.root)[0]
        self.assertIn("Manifest label thm:one occurs 2 times", errors)
        self.assertIn("Stale manifest row: lem:old", errors)

    def test_conjecture_cannot_be_marked_checked(self):
        self.paper.write_text(r"\begin{conjecture}\label{conj:one}Claim.\end{conjecture}")
        self.manifest.write_text("| `conj:one` | Claim | checked | `provedOne` |\n")
        self.assertIn("Conjecture status mismatch: conj:one", check_manifest(self.root)[0])

    def test_checked_row_requires_declaration(self):
        self.manifest.write_text("| `thm:one` | Claim | checked | Not supplied |\n")
        self.assertTrue(any("named Lean declaration" in error for error in check_manifest(self.root)[0]))

    def test_orphaned_module_and_placeholder_are_rejected(self):
        (self.root / "KLocality").mkdir()
        module = self.root / "KLocality" / "Example.lean"
        module.write_text("theorem example_claim : True := by trivial\n")
        umbrella = self.root / "KLocality.lean"
        umbrella.write_text("")
        self.assertTrue(any("imports missing" in error for error in check_sources(self.root)))
        umbrella.write_text("import KLocality.Example\n")
        self.assertEqual(check_sources(self.root), [])
        module.write_text("theorem example_claim : False := by sorry\n")
        self.assertTrue(any("proof placeholder" in error for error in check_sources(self.root)))

    def test_links_resolve_from_containing_document(self):
        (self.root / "docs").mkdir()
        guide = self.root / "docs" / "guide.md"
        guide.write_text("[paper](../main.tex) [section](#local) [web](https://example.org)\n")
        self.assertEqual(check_links(self.root), [])
        guide.write_text("[old paper](../removed.tex)\n")
        self.assertTrue(any("missing link target" in error for error in check_links(self.root)))

    def test_unresolved_references_and_overflow_fail(self):
        log = self.root / "main.log"
        log.write_text("Output written on main.pdf (1 page).\n")
        self.assertEqual(check_tex_log(log), [])
        log.write_text("LaTeX Warning: There were undefined references.\n"
                       "Overfull \\hbox (10.0pt too wide) detected\n")
        self.assertEqual(len(check_tex_log(log)), 2)


if __name__ == "__main__":
    unittest.main()
