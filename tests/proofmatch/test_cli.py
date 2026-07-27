import io
import tempfile
import unittest
from contextlib import redirect_stdout
from decimal import Decimal
from pathlib import Path
from unittest.mock import patch

from proofmatch.artifacts import RunStore
from proofmatch.cli import (
    apply_upstream_manifest,
    build_parser,
    main,
    select_primary_candidate,
    write_difference_report,
)
from proofmatch.models import (
    Candidate,
    DocumentBlock,
    DocumentIndex,
    ProofStepAssignment,
    ProofStepManifest,
)


VALIDATED = """
<!-- generated-by: proofmatch Codex repair -->
<!-- source-pdf-sha256: abcdef1234567890 -->

<a id="pdf-abcdef123456-p001-b001"></a>
<!-- pdf-source: page=1; block=1; confidence=0.99 -->
## Håstad's Switching Lemma
A width-w DNF under a random restriction has a shallow decision tree.
""".lstrip()


class CliTests(unittest.TestCase):
    def test_parser_exposes_upstream_mapping_commands(self):
        mapping = build_parser().parse_args(
            ["map-upstream", "abcdef123456", "--max-cost", "1.00", "--dry-run"]
        )
        review = build_parser().parse_args(
            ["review-upstream", "abcdef123456"]
        )

        self.assertEqual(mapping.command, "map-upstream")
        self.assertTrue(mapping.dry_run)
        self.assertEqual(review.command, "review-upstream")

        with self.assertRaises(SystemExit):
            build_parser().parse_args(
                ["review-upstream", "abcdef123456", "approve"]
            )

    def test_validated_manifest_writes_steps_without_second_approval(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "entry.tex"
            path.write_text(
                "\\begin{theorem}\n"
                "\\lean{T.target}\n"
                "Claim.\n"
                "\\end{theorem}\n",
                encoding="utf-8",
            )
            manifest = ProofStepManifest(
                theorem="T.target",
                document="notes",
                source_fingerprint="source",
                proof_fingerprint="proof",
                dependency_fingerprint="dependencies",
                assignments=(
                    ProofStepAssignment(
                        "T.helper",
                        "context",
                        ("pdf-abcdef123456-p002-b001",),
                        "Supports this proof step.",
                    ),
                ),
            )

            apply_upstream_manifest(path, manifest)

            self.assertIn(
                "\\proofstep\n"
                "  {T.helper}\n"
                "  {context}\n"
                "  {notes}\n"
                "  {pdf-abcdef123456-p002-b001}",
                path.read_text(encoding="utf-8"),
            )

    def test_map_upstream_requires_theorem_level_approval(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            store = RunStore(root, "abcdef123456")
            store.write_json(
                "review",
                {
                    "verdict": {"verdict": "same"},
                    "candidate": {"lean_name": "SwitchingLemma2.switching_lemma"},
                },
            )
            store.write_json("decision", {"decision": "defer"})

            with patch("proofmatch.cli.WORK_ROOT", root):
                with self.assertRaisesRegex(ValueError, "theorem-level approval"):
                    main(
                        [
                            "map-upstream",
                            "abcdef123456",
                            "--max-cost",
                            "1.00",
                            "--dry-run",
                        ]
                    )

    def test_map_upstream_dry_run_writes_no_manifest(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            store = RunStore(root, "abcdef123456")
            store.write_json(
                "review",
                {
                    "source_markdown": str(
                        Path(
                            "blueprint/src/references/switching-lemma.md"
                        ).resolve()
                    ),
                    "document": "switching-lemma",
                    "candidate": {
                        "lean_name": "SwitchingLemma2.switching_lemma",
                        "proof": "by exact True.intro",
                    },
                    "verdict": {
                        "verdict": "same",
                        "document_blocks": [
                            "pdf-b5e074215b9e-p001-b008",
                            "pdf-b5e074215b9e-p002-b001",
                            "pdf-b5e074215b9e-p002-b002",
                            "pdf-b5e074215b9e-p002-b003",
                            "pdf-b5e074215b9e-p002-b004",
                        ],
                    },
                    "estimated_spend_usd": "0.199915",
                },
            )
            store.write_json("decision", {"decision": "approve"})

            with patch("proofmatch.cli.WORK_ROOT", root):
                result = main(
                    [
                        "map-upstream",
                        "abcdef123456",
                        "--max-cost",
                        "5.00",
                        "--dry-run",
                    ]
                )

            self.assertEqual(result, 0)
            self.assertFalse(store.stage_path("proof_steps").exists())
            self.assertFalse(
                store.stage_path("proof_steps_review", ".md").exists()
            )

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
