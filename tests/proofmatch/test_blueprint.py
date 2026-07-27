import tempfile
import unittest
from pathlib import Path

from proofmatch.blueprint import (
    SourceProposal,
    StepProposal,
    apply_blueprint_mutations,
    ProofSource,
    ProofStep,
    insert_approved_steps,
    insert_approved_source,
    parse_proof_steps,
    parse_proof_sources,
    plan_blueprint_mutations,
)
from scripts.build_dataset import (
    display_output_path,
    order_proof_steps,
    parse_blueprint,
)


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
    def test_batch_source_planning_is_idempotent(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "A.tex"
            path.write_text(
                "\\begin{theorem}\n\\lean{T.one}\nClaim.\n\\end{theorem}\n",
                encoding="utf-8",
            )
            proposal = SourceProposal(
                path, "T.one",
                ProofSource("notes", ("pdf-abcdef123456-p001-b001",)),
            )
            apply_blueprint_mutations(plan_blueprint_mutations((proposal,)))
            self.assertEqual(plan_blueprint_mutations((proposal,)), ())

    def test_batch_plans_proof_steps(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "A.tex"
            path.write_text(
                "\\begin{theorem}\n\\lean{T.one}\nClaim.\n\\end{theorem}\n",
                encoding="utf-8",
            )
            proposal = StepProposal(
                path,
                "T.one",
                (ProofStep(
                    "T.helper", "context", "notes",
                    ("pdf-abcdef123456-p001-b001",),
                ),),
            )
            mutations = plan_blueprint_mutations((proposal,))
            self.assertIn("\\proofstep", mutations[0].updated)

    def test_conflict_in_batch_writes_no_files(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            a, b = root / "A.tex", root / "B.tex"
            a.write_text(
                "\\begin{theorem}\n\\lean{T.a}\nA.\n\\end{theorem}\n",
                encoding="utf-8",
            )
            b.write_text(
                "\\begin{theorem}\n\\lean{T.b}\n"
                "\\proofsource{notes}{pdf-abcdef123456-p001-b001}\n"
                "B.\n\\end{theorem}\n",
                encoding="utf-8",
            )
            before_a, before_b = a.read_text(), b.read_text()
            proposals = (
                SourceProposal(a, "T.a", ProofSource(
                    "notes", ("pdf-abcdef123456-p001-b001",)
                )),
                SourceProposal(b, "T.b", ProofSource(
                    "notes", ("pdf-abcdef123456-p002-b001",)
                )),
            )
            with self.assertRaisesRegex(ValueError, "proof-source conflict"):
                plan_blueprint_mutations(proposals)
            self.assertEqual(a.read_text(), before_a)
            self.assertEqual(b.read_text(), before_b)

    def test_dataset_parser_emits_steps_without_leaking_macros_into_prose(self):
        with tempfile.TemporaryDirectory() as tmp:
            chapter = Path(tmp)
            (chapter / "entry.tex").write_text(
                PROOF_STEP_FIXTURE,
                encoding="utf-8",
            )

            record = parse_blueprint(chapter)[
                "SwitchingLemma2.switching_lemma"
            ]

            self.assertEqual(
                record["proof_steps"],
                [
                    {
                        "lean_name": "SwitchingLemma2.canonicalDTree_correct",
                        "relation": "context",
                        "document": "switching-lemma",
                        "blocks": ["pdf-abcdef123456-p002-b001"],
                    }
                ],
            )
            self.assertNotIn("\\proofstep", record["informal"])

    def test_dataset_orders_steps_by_proof_dependency_sequence(self):
        steps = [
            {
                "lean_name": "T.second",
                "relation": "context",
                "document": "notes",
                "blocks": ["pdf-abcdef123456-p002-b002"],
            },
            {
                "lean_name": "T.first",
                "relation": "direct",
                "document": "notes",
                "blocks": ["pdf-abcdef123456-p002-b001"],
            },
        ]

        ordered = order_proof_steps(steps, ["T.first", "T.second"])

        self.assertEqual(
            [step["lean_name"] for step in ordered],
            ["T.first", "T.second"],
        )

    def test_dataset_rejects_duplicate_step_declarations(self):
        duplicate = {
            "lean_name": "T.first",
            "relation": "context",
            "document": "notes",
            "blocks": ["pdf-abcdef123456-p002-b001"],
        }

        with self.assertRaisesRegex(ValueError, r"duplicate.*T\.first"):
            order_proof_steps(
                [duplicate, dict(duplicate)],
                ["T.first"],
            )

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
