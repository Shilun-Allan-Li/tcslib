import subprocess
import tempfile
import unittest
from pathlib import Path

from proofmatch.extraction import (
    diagnose_page,
    extract_pdf,
    format_raw_markdown,
    split_pages,
)


class ExtractionTests(unittest.TestCase):
    def test_writes_faithful_page_delimited_raw_markdown(self):
        pages = ["Theorem 1\nA → B", "Proof\nB follows."]

        markdown = format_raw_markdown(
            "abc123",
            "pdfminer.six v20260107",
            pages,
        )

        self.assertIn("source-pdf-sha256: abc123", markdown)
        self.assertIn("extractor: pdfminer.six v20260107", markdown)
        self.assertIn("<!-- pdf-page: 1 -->\nTheorem 1\nA → B", markdown)
        self.assertIn("<!-- pdf-page: 2 -->\nProof\nB follows.", markdown)

    def test_form_feed_split_drops_only_terminal_empty_page(self):
        self.assertEqual(split_pages("first\fsecond\f"), ["first", "second"])
        self.assertEqual(split_pages("first\f\fthird"), ["first", "", "third"])

    def test_flags_fragmented_math_without_rewriting_it(self):
        text = "f :\n{0,1}\nn\n→\n{0,1}\nLecture-1"

        diagnostic = diagnose_page(1, text)

        self.assertIn("fragmented-lines", diagnostic.reasons)
        self.assertIn("detached-math-symbols", diagnostic.reasons)
        self.assertLess(diagnostic.confidence, 1.0)

    def test_extract_invokes_local_tool_and_records_report(self):
        calls = []

        def runner(command, **kwargs):
            calls.append((command, kwargs))
            if command == ["pdf2txt.py", "--version"]:
                return subprocess.CompletedProcess(command, 0, "pdfminer.six v1\n", "")
            self.assertEqual(command[:3], ["pdf2txt.py", "-o", "-"])
            return subprocess.CompletedProcess(command, 0, "Page one\fPage two\f", "")

        with tempfile.TemporaryDirectory() as tmp:
            pdf = Path(tmp) / "notes.pdf"
            pdf.write_bytes(b"%PDF-fixture")
            output = Path(tmp) / "notes.raw.md"

            report = extract_pdf(pdf, output, runner=runner)

            self.assertEqual(report.page_count, 2)
            self.assertEqual(report.source_pdf, str(pdf))
            self.assertIn("<!-- pdf-page: 2 -->\nPage two", output.read_text())
            self.assertEqual(len(calls), 2)


if __name__ == "__main__":
    unittest.main()
