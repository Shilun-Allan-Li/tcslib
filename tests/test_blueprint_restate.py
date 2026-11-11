import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from scripts import blueprint_restate as restate
from scripts import dataset_check


class RestateTests(unittest.TestCase):
    def test_doubled_commands_are_rejected_without_breaking_tex_row_breaks(self):
        for text in (r"$\\rho$", r"$\\mathbb{R}$", r"$x\\,y$", r"$\\\\rho$"):
            with self.subTest(text=text):
                self.assertTrue(restate.Q.overescaped_latex(text))
                self.assertFalse(restate.Q.typesets(text))
        for text in (r"$\rho\in\mathbb{R}$", r"$x\,y$",
                     r"\begin{matrix}a&b\\c&d\end{matrix}",
                     r"\begin{aligned}x&=1\\[4pt]y&=2\end{aligned}",
                     r"\begin{matrix}x\\\rho\end{matrix}"):
            with self.subTest(text=text):
                self.assertFalse(restate.Q.overescaped_latex(text))
                self.assertTrue(restate.Q.typesets(text))

    def test_noise_definition_cache_cannot_overwrite_repaired_tex(self):
        body = (r"For a natural number $n$, a real parameter $\rho$, a function "
                r"$f:\mathbb{R}^n\to\mathbb{R}$, and $x\in\mathbb{R}^n$, "
                r"the Gaussian noise operator at $x$ is the Gaussian average of "
                r"$f\bigl(\rho x+\sqrt{1-\rho^2}Y\bigr)$, where $Y$ "
                "has independent standard Gaussian coordinates.")
        entry = {"statement": body.replace("\\", "\\\\"),
                 "replaced": "% dataset-pipeline: stub -- prose pending"}
        result, report, backups = self.apply({"sample": entry}, body=body)
        self.assertIn(body, result)
        self.assertNotIn(r"\\rho", result)
        self.assertFalse(backups)
        self.assertIn(("sample.tex", "sample", "latex-unsafe"), report)

    def test_strict_checks_doubled_commands_in_definitions(self):
        record = {"title": r"Noise $\\rho$", "definitions":
                  [{"informal": r"Let $f:\\mathbb{R}^n\\to\\mathbb{R}$."}]}
        self.assertEqual(dataset_check.corrupt_prose_fields(record, restate.Q.overescaped_latex),
                         ["title", "definitions[0].informal"])
        self.assertIn("latex-escape", dataset_check.HARD)

    def test_dataset_strict_rejects_corrupt_prose_and_inherited_definitions(self):
        record = {"title": "Bad\x1b[0mtitle", "informal_statement": "Bad \x08br.",
                  "informal_proof": "Bad \ufffd.",
                  "definitions": [{"title": "Valid", "informal": "Bad \x00phi."}]}
        self.assertEqual(dataset_check.corrupt_prose_fields(record),
                         ["title", "informal_statement", "informal_proof", "definitions[0].informal"])
        self.assertIn("corrupt-text", dataset_check.HARD)

    def apply(self, entries, body=r"Let $x$ be real. Then $x = x$.", names="sample",
              persist=True):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            tex = root / "sample.tex"
            original = ("\\begin{theorem}[Original title]\n"
                        "\\lean{" + names + "}\n\\leanok\n" + body +
                        "\n\\end{theorem}\n")
            tex.write_text(original)
            report = []
            with patch.object(restate.cache, "CACHE_DIR", root):
                result = restate.apply_cached(tex, entries, report, persist=persist)
            backups = list(root.glob("*.json"))
            return result or original, report, bool(backups)

    def test_controls_are_rejected_by_generation_and_apply_guard(self):
        for code in (*range(0, 9), 11, 12, *range(14, 32), *range(127, 160), 0xfffd):
            statement = "Let $x$ be real. Then $x = " + chr(code) + "x$."
            with self.subTest(code=code):
                self.assertFalse(restate.Q.typesets(statement))
                self.assertIn("latex-unsafe", restate.Q.check(statement))
                result, report, _ = self.apply({"sample": {"statement": statement}})
                self.assertNotIn(chr(code), result)
                self.assertIn(("sample.tex", "sample", "latex-unsafe"), report)

    def test_bad_cache_does_not_replace_repaired_prose_with_stub(self):
        entry = {"statement": "Bad \x08br text.", "replaced":
                 "% dataset-pipeline: stub -- prose pending\nStatement pending regeneration."}
        result, report, _ = self.apply({"sample": entry})
        self.assertIn("Then $x = x$", result)
        self.assertNotIn("reverted", [r[2] for r in report])

    def test_safe_backup_is_restored_and_written(self):
        entry = {"statement": "Bad \x08br text.", "replaced": "Every real number equals itself."}
        result, report, _ = self.apply({"sample": entry}, body=entry["statement"])
        self.assertIn(entry["replaced"], result)
        self.assertNotIn("\x08", result)
        self.assertIn(("sample.tex", "sample", "reverted"), report)

    def test_corrupted_backup_is_never_restored(self):
        entry = {"statement": "Bad \x08br text.", "replaced": "Also bad \x00phi."}
        result, report, _ = self.apply({"sample": entry})
        self.assertNotIn("\x00", result)
        self.assertNotIn("reverted", [r[2] for r in report])

    def test_group_rejects_all_statements_if_one_is_corrupted(self):
        entries = {"sample": {"statement": "A safe replacement."},
                   "other": {"statement": "Bad \x1b[0m text."}}
        result, report, backups = self.apply(entries, names="sample, other")
        self.assertIn("Then $x = x$", result)
        self.assertNotIn("A safe replacement", result)
        self.assertFalse(backups)

    def test_title_is_checked_before_whitespace_normalization(self):
        for title in ("Broken\x0ctitle", "Broken\x1b[0mtitle", r"Broken $\unknown$", "Broken $"):
            with self.subTest(title=title):
                entry = {"statement": "Every real number equals itself.", "title": title}
                result, report, _ = self.apply({"sample": entry})
                self.assertIn("[Original title]", result)
                self.assertIn(("sample.tex", "sample", "title-unsafe"), report)
                self.assertIn("title-unsafe", restate.Q.check(entry["statement"], title))

    def test_valid_tex_survives_and_second_application_is_identical(self):
        entry = {"statement": r"Let $\alpha\in\mathbb{R}$. Then $\alpha\le\alpha$.",
                 "title": "Real equality"}
        first, _, _ = self.apply({"sample": entry})
        self.assertIn(entry["statement"], first)
        second, _, _ = self.apply({"sample": entry})
        self.assertEqual(first, second)

    def test_check_does_not_write_single_or_grouped_cache_backups(self):
        for names in ("sample", "sample, other"):
            entries = {name: {"statement": "Every real number equals itself."}
                       for name in ("sample", "other")}
            _, _, backups = self.apply(entries, names=names, persist=False)
            self.assertFalse(backups)


if __name__ == "__main__":
    unittest.main()
