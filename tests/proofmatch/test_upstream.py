import unittest
from decimal import Decimal
from pathlib import Path

from proofmatch.models import (
    DocumentBlock,
    DocumentIndex,
    ProofStepAssignment,
    ProofStepManifest,
    UpstreamDeclaration,
)
from proofmatch.upstream import (
    batch_declarations,
    build_manifest,
    estimate_upstream_batches,
    load_upstream_declarations,
    map_upstream_batches,
    render_upstream_review,
    validate_assignments,
    validate_manifest,
)
from proofmatch.budget import Budget


BLOCK_1 = "pdf-abcdef123456-p002-b001"
BLOCK_2 = "pdf-abcdef123456-p002-b002"


def declaration(name: str) -> UpstreamDeclaration:
    return UpstreamDeclaration(
        lean_name=name,
        kind="lemma",
        statement=f"Statement of {name}",
        source_module="TCSlib.Test",
        direct_dependencies=(),
        proof_excerpt="by simp",
    )


def assignment(
    name: str,
    relation: str = "context",
    blocks: tuple[str, ...] = (BLOCK_1,),
) -> ProofStepAssignment:
    return ProofStepAssignment(
        lean_name=name,
        relation=relation,
        document_blocks=blocks,
        rationale=f"{name} supports this proof step.",
    )


class FakeAgent:
    def __init__(self, outputs):
        self.outputs = list(outputs)

    def run(self, prompt_name, payload):
        if prompt_name != "map_upstream":
            raise AssertionError(prompt_name)
        return self.outputs.pop(0)


def block(block_id: str = BLOCK_1, markdown: str = "Proof step.") -> DocumentBlock:
    return DocumentBlock(
        block_id,
        2,
        1,
        "proof",
        "Proof",
        markdown,
        0.99,
    )


class UpstreamTests(unittest.TestCase):
    def test_agent_must_return_exact_batch_names(self):
        agent = FakeAgent(
            [
                {
                    "assignments": [
                        {
                            "lean_name": "T.first",
                            "relation": "context",
                            "document_blocks": [BLOCK_1],
                            "rationale": "Supports the canonical-tree construction.",
                        }
                    ]
                }
            ]
        )

        with self.assertRaisesRegex(ValueError, r"missing.*T\.second"):
            map_upstream_batches(
                (declaration("T.first"), declaration("T.second")),
                (block(),),
                agent,
                Budget(Decimal("1.00")),
            )

    def test_manifest_rejects_changed_markdown_proof_or_dependency_order(self):
        declarations = (declaration("T.first"), declaration("T.second"))
        assignments = (
            assignment("T.first", relation="direct"),
            assignment("T.second"),
        )
        index = DocumentIndex(
            "abcdef1234567890",
            (block(),),
            (),
        )
        manifest = build_manifest(
            "T.target",
            "notes",
            index,
            "by exact T.second",
            declarations,
            assignments,
        )

        validate_manifest(
            manifest,
            index,
            "by exact T.second",
            declarations,
            {BLOCK_1},
        )
        with self.subTest("markdown"):
            changed_index = DocumentIndex("changed", index.blocks, ())
            with self.assertRaisesRegex(ValueError, "Markdown"):
                validate_manifest(
                    manifest,
                    changed_index,
                    "by exact T.second",
                    declarations,
                    {BLOCK_1},
                )
        with self.subTest("proof"):
            with self.assertRaisesRegex(ValueError, "proof"):
                validate_manifest(
                    manifest,
                    index,
                    "by exact T.first",
                    declarations,
                    {BLOCK_1},
                )
        with self.subTest("dependencies"):
            with self.assertRaisesRegex(ValueError, "dependency"):
                validate_manifest(
                    manifest,
                    index,
                    "by exact T.second",
                    tuple(reversed(declarations)),
                    {BLOCK_1},
                )

    def test_review_groups_adjacent_equal_mappings_without_losing_names(self):
        manifest = ProofStepManifest(
            theorem="T.target",
            document="notes",
            source_fingerprint="abcdef1234567890",
            proof_fingerprint="proof",
            dependency_fingerprint="deps",
            assignments=(
                assignment("T.first"),
                assignment("T.second"),
                assignment("T.third", relation="direct", blocks=(BLOCK_2,)),
            ),
        )

        review = render_upstream_review(
            manifest,
            {
                BLOCK_1: block(BLOCK_1, "Canonical tree."),
                BLOCK_2: block(BLOCK_2, "Counting."),
            },
        )

        self.assertIn("3/3 (100%)", review)
        self.assertIn("2 contextual declarations", review)
        self.assertIn("T.first", review)
        self.assertIn("T.second", review)
        self.assertIn("T.third", review)

    def test_loader_preserves_live_proof_upstream_order_and_excludes_target(self):
        result = load_upstream_declarations(
            Path("dataset/tcslib_theorems.jsonl"),
            Path("dep_graph.json"),
            "SwitchingLemma2.switching_lemma",
        )

        self.assertEqual(len(result), 173)
        self.assertEqual(
            [item.lean_name for item in result[:3]],
            ["BoolCircuit.Lit", "BoolCircuit.Lit.eval", "Literal"],
        )
        self.assertNotIn(
            "SwitchingLemma2.switching_lemma",
            [item.lean_name for item in result],
        )
        self.assertEqual(
            result[0].source_module,
            "TCSlib.BooleanAnalysis.Switching.Circuit",
        )

    def test_batching_is_deterministic_and_never_splits_a_record(self):
        first = declaration("T.first")
        second = declaration("T.second")
        first = UpstreamDeclaration(
            **{**first.__dict__, "proof_excerpt": "a" * 30}
        )
        second = UpstreamDeclaration(
            **{**second.__dict__, "proof_excerpt": "b" * 30}
        )

        batches = batch_declarations(
            (first, second),
            max_characters=240,
        )

        self.assertEqual(
            [[item.lean_name for item in batch] for batch in batches],
            [["T.first"], ["T.second"]],
        )

    def test_mapping_estimate_reserves_output_for_each_declaration(self):
        proof_block = DocumentBlock(
            BLOCK_1,
            2,
            1,
            "proof",
            "Proof",
            "Canonical decision tree.",
            0.99,
        )

        estimates = estimate_upstream_batches(
            ((declaration("T.first"), declaration("T.second")),),
            (proof_block,),
        )

        self.assertEqual(len(estimates), 1)
        self.assertEqual(estimates[0].output_tokens, 320)
        self.assertGreater(estimates[0].input_tokens, 0)
        self.assertGreater(estimates[0].usd, Decimal("0"))

    def test_validation_requires_every_dependency_once_in_closure_order(self):
        result = validate_assignments(
            (declaration("T.first"), declaration("T.second")),
            (
                assignment("T.second", blocks=(BLOCK_2,)),
                assignment("T.first", relation="direct", blocks=(BLOCK_1,)),
            ),
            {BLOCK_1, BLOCK_2},
        )

        self.assertEqual(
            [item.lean_name for item in result],
            ["T.first", "T.second"],
        )

    def test_validation_rejects_incomplete_coverage(self):
        with self.assertRaisesRegex(ValueError, r"missing.*T\.second"):
            validate_assignments(
                (declaration("T.first"), declaration("T.second")),
                (assignment("T.first"),),
                {BLOCK_1},
            )

    def test_validation_rejects_duplicate_declarations(self):
        with self.assertRaisesRegex(ValueError, r"duplicate.*T\.first"):
            validate_assignments(
                (declaration("T.first"),),
                (assignment("T.first"), assignment("T.first")),
                {BLOCK_1},
            )

    def test_validation_rejects_unknown_declarations(self):
        with self.assertRaisesRegex(ValueError, r"unknown.*T\.other"):
            validate_assignments(
                (declaration("T.first"),),
                (assignment("T.first"), assignment("T.other")),
                {BLOCK_1},
            )

    def test_validation_rejects_blocks_outside_proof_context(self):
        with self.assertRaisesRegex(ValueError, r"T\.first.*p099-b999"):
            validate_assignments(
                (declaration("T.first"),),
                (
                    assignment(
                        "T.first",
                        blocks=("pdf-abcdef123456-p099-b999",),
                    ),
                ),
                {BLOCK_1},
            )

    def test_validation_rejects_empty_block_lists(self):
        with self.assertRaisesRegex(ValueError, r"T\.first.*at least one"):
            validate_assignments(
                (declaration("T.first"),),
                (assignment("T.first", blocks=()),),
                {BLOCK_1},
            )


if __name__ == "__main__":
    unittest.main()
