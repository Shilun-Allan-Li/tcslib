import io
import tempfile
import unittest
from contextlib import redirect_stdout
from decimal import Decimal
from pathlib import Path

from proofmatch.artifacts import RunStore
from proofmatch.cli import (
    build_parser,
    main,
    select_primary_candidate,
    write_difference_report,
)
from proofmatch.models import Candidate, DocumentBlock, DocumentIndex


VALIDATED = """
<!-- generated-by: proofmatch Codex repair -->
<!-- source-pdf-sha256: abcdef1234567890 -->

<a id="pdf-abcdef123456-p001-b001"></a>
<!-- pdf-source: page=1; block=1; confidence=0.99 -->
## Håstad's Switching Lemma
A width-w DNF under a random restriction has a shallow decision tree.
""".lstrip()


class CliTests(unittest.TestCase):
    def test_same_rerun_removes_stale_difference_report(self):
        with tempfile.TemporaryDirectory() as tmp:
            store = RunStore(Path(tmp), "abcdef123456")
            stale = store.stage_path("differences", ".md")
            stale.parent.mkdir(parents=True)
            stale.write_text("old uncertainty", encoding="utf-8")

            result = write_difference_report(store, None)

            self.assertIsNone(result)
            self.assertFalse(stale.exists())

    def test_primary_match_follows_document_order_not_reranker_confidence(self):
        def candidate(name, blocks):
            return Candidate(name, name, "M", "", "", "", 1, 1.0, blocks)

        early = candidate("T.switching_lemma", ("pdf-abcdef123456-p001-b002",))
        later = candidate("T.helper", ("pdf-abcdef123456-p003-b002",))
        index = DocumentIndex(
            "abcdef123456",
            (
                DocumentBlock("pdf-abcdef123456-p001-b002", 1, 2, "theorem", "", "", 1),
                DocumentBlock("pdf-abcdef123456-p003-b002", 3, 2, "theorem", "", "", 1),
            ),
            (),
        )
        reranked = {
            "candidates": [
                # Agent-cited blocks are evidence, not authority for deterministic
                # source ordering; they may be overly broad or mistaken.
                {"lean_name": "T.helper", "block_ids": ["pdf-abcdef123456-p001-b002"]},
                {"lean_name": "T.switching_lemma", "block_ids": ["pdf-abcdef123456-p003-b002"]},
            ]
        }

        selected = select_primary_candidate([early, later], reranked, index)

        self.assertEqual(selected.lean_name, "T.switching_lemma")

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
