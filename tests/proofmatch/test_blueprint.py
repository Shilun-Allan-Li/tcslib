import tempfile
import unittest
from pathlib import Path

from proofmatch.blueprint import (
    ProofSource,
    ProofStep,
    insert_approved_steps,
    insert_approved_source,
    parse_proof_steps,
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

PROOF_STEP_FIXTURE = r"""
\begin{theorem}[Switching Lemma]
\lean{SwitchingLemma2.switching_lemma}
\leanok
\proofsource{switching-lemma}{pdf-abcdef123456-p002-b001}
\proofstep
  {SwitchingLemma2.canonicalDTree_correct}
  {context}
  {switching-lemma}
  {pdf-abcdef123456-p002-b001}
Statement.
\end{theorem}
"""


class BlueprintTests(unittest.TestCase):
    def test_parses_multiline_proof_steps_in_theorem_environment(self):
        parsed = parse_proof_steps(PROOF_STEP_FIXTURE)

        steps = parsed["SwitchingLemma2.switching_lemma"]
        self.assertEqual(len(steps), 1)
        self.assertEqual(
            steps[0].lean_name,
            "SwitchingLemma2.canonicalDTree_correct",
        )
        self.assertEqual(steps[0].relation, "context")
        self.assertEqual(steps[0].document, "switching-lemma")
        self.assertEqual(
            steps[0].blocks,
            ("pdf-abcdef123456-p002-b001",),
        )

    def test_identical_step_reapproval_is_idempotent(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "entry.tex"
            path.write_text(PROOF_STEP_FIXTURE, encoding="utf-8")
            steps = (
                ProofStep(
                    "SwitchingLemma2.canonicalDTree_correct",
                    "context",
                    "switching-lemma",
                    ("pdf-abcdef123456-p002-b001",),
                ),
            )

            insert_approved_steps(
                path,
                "SwitchingLemma2.switching_lemma",
                steps,
                approved=True,
            )
            once = path.read_text(encoding="utf-8")
            insert_approved_steps(
                path,
                "SwitchingLemma2.switching_lemma",
                steps,
                approved=True,
            )

            self.assertEqual(path.read_text(encoding="utf-8"), once)

    def test_conflicting_existing_step_is_preserved_and_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "entry.tex"
            path.write_text(PROOF_STEP_FIXTURE, encoding="utf-8")
            original = path.read_text(encoding="utf-8")
            changed = (
                ProofStep(
                    "SwitchingLemma2.canonicalDTree_correct",
                    "direct",
                    "switching-lemma",
                    ("pdf-abcdef123456-p002-b001",),
                ),
            )

            with self.assertRaisesRegex(
                ValueError,
                r"conflict.*canonicalDTree_correct",
            ):
                insert_approved_steps(
                    path,
                    "SwitchingLemma2.switching_lemma",
                    changed,
                    approved=True,
                )

            self.assertEqual(path.read_text(encoding="utf-8"), original)

    def test_unapproved_steps_cannot_write_blueprint(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "entry.tex"
            path.write_text(PROOF_STEP_FIXTURE, encoding="utf-8")
            original = path.read_text(encoding="utf-8")

            with self.assertRaisesRegex(PermissionError, "explicit approval"):
                insert_approved_steps(
                    path,
                    "SwitchingLemma2.switching_lemma",
                    (
                        ProofStep(
                            "T.helper",
                            "context",
                            "switching-lemma",
                            ("pdf-abcdef123456-p002-b001",),
                        ),
                    ),
                    approved=False,
                )

            self.assertEqual(path.read_text(encoding="utf-8"), original)

    def test_new_step_is_separated_from_existing_source_metadata(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "entry.tex"
            path.write_text(
                "\\begin{theorem}\n"
                "\\lean{T.target}\n"
                "\\proofsource{notes}{pdf-abcdef123456-p002-b001}\n"
                "Statement.\n"
                "\\end{theorem}\n",
                encoding="utf-8",
            )

            insert_approved_steps(
                path,
                "T.target",
                (
                    ProofStep(
                        "T.helper",
                        "context",
                        "notes",
                        ("pdf-abcdef123456-p002-b001",),
                    ),
                ),
                approved=True,
            )

            self.assertIn(
                "\\proofsource{notes}{pdf-abcdef123456-p002-b001}\n"
                "\\proofstep\n",
                path.read_text(encoding="utf-8"),
            )

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
