import tempfile
import unittest
from pathlib import Path

from proofmatch.blueprint import (
    ProofSource,
    insert_approved_source,
    parse_proof_sources,
)
from scripts.build_dataset import display_output_path


FIXTURE = r"""
\begin{theorem}[Switching Lemma]
\lean{SwitchingLemma2.switching_lemma}
\leanok
\proofsource{switching-lemma}{
  pdf-abcdef123456-p002-b003,
  pdf-abcdef123456-p003-b001
}
Statement.
\end{theorem}
"""


class BlueprintTests(unittest.TestCase):
    def test_dataset_output_display_accepts_paths_outside_repository(self):
        self.assertEqual(
            display_output_path(Path("/tmp/proofmatch-dataset.jsonl"), Path("/repo")),
            "/tmp/proofmatch-dataset.jsonl",
        )

    def test_parses_multiblock_source_bound_to_lean_environment(self):
        parsed = parse_proof_sources(FIXTURE)

        source = parsed["SwitchingLemma2.switching_lemma"][0]
        self.assertEqual(source.document, "switching-lemma")
        self.assertEqual(
            source.blocks,
            (
                "pdf-abcdef123456-p002-b003",
                "pdf-abcdef123456-p003-b001",
            ),
        )

    def test_deferred_decision_cannot_write_blueprint(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "entry.tex"
            path.write_text(FIXTURE, encoding="utf-8")

            with self.assertRaisesRegex(PermissionError, "explicit approval"):
                insert_approved_source(
                    path,
                    "SwitchingLemma2.switching_lemma",
                    ProofSource("other-notes", ("pdf-abcdef123456-p001-b001",)),
                    approved=False,
                )

    def test_approved_source_is_inserted_after_leanok(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "entry.tex"
            path.write_text(
                "\\begin{theorem}\n"
                "\\lean{T.foo}\n"
                "\\leanok\n"
                "Claim.\n"
                "\\end{theorem}\n",
                encoding="utf-8",
            )

            insert_approved_source(
                path,
                "T.foo",
                ProofSource(
                    "switching-lemma",
                    ("pdf-abcdef123456-p002-b003",),
                ),
                approved=True,
            )

            text = path.read_text(encoding="utf-8")
            self.assertIn(
                "\\leanok\n"
                "\\proofsource{switching-lemma}{pdf-abcdef123456-p002-b003}\n",
                text,
            )


if __name__ == "__main__":
    unittest.main()
