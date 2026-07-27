import io
import tempfile
import unittest
from contextlib import redirect_stdout
from decimal import Decimal
from pathlib import Path

from proofmatch.cli import build_parser, main


VALIDATED = """
<!-- generated-by: proofmatch Codex repair -->
<!-- source-pdf-sha256: abcdef1234567890 -->

<a id="pdf-abcdef123456-p001-b001"></a>
<!-- pdf-source: page=1; block=1; confidence=0.99 -->
## Håstad's Switching Lemma
A width-w DNF under a random restriction has a shallow decision tree.
""".lstrip()


class CliTests(unittest.TestCase):
    def test_fixture_run_defaults_to_one_dollar(self):
        args = build_parser().parse_args(
            ["run", "blueprint/src/references/switching-lemma.pdf"]
        )

        self.assertEqual(args.max_cost, Decimal("1.00"))

    def test_nonfixture_run_requires_explicit_budget(self):
        with tempfile.TemporaryDirectory() as tmp:
            pdf = Path(tmp) / "other.pdf"
            pdf.write_bytes(b"%PDF")

            with self.assertRaisesRegex(ValueError, "--max-cost"):
                main(["run", str(pdf), "--dry-run"])

    def test_match_starts_from_validated_markdown_without_pdf_extraction(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            markdown = root / "notes.md"
            markdown.write_text(VALIDATED, encoding="utf-8")
            dataset = root / "data.jsonl"
            dataset.write_text(
                '{"id":"SwitchingLemma2.switching_lemma",'
                '"lean_name":"SwitchingLemma2.switching_lemma",'
                '"title":"Switching Lemma","source_module":"TCSlib.X",'
                '"statement_informal":"A DNF restriction has shallow decision tree",'
                '"formal_statement":"theorem switching_lemma : True",'
                '"proof":"by trivial"}\n',
                encoding="utf-8",
            )
            output = io.StringIO()

            with redirect_stdout(output):
                exit_code = main(
                    [
                        "match",
                        str(markdown),
                        "--dataset",
                        str(dataset),
                        "--dry-run",
                        "--max-cost",
                        "1.00",
                    ]
                )

            self.assertEqual(exit_code, 0)
            self.assertIn("SwitchingLemma2.switching_lemma", output.getvalue())
            self.assertFalse((root / "notes.raw.md").exists())


if __name__ == "__main__":
    unittest.main()
