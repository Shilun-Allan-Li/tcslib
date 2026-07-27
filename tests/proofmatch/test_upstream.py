import unittest
from decimal import Decimal
from pathlib import Path

from proofmatch.models import (
    DocumentBlock,
    ProofStepAssignment,
    UpstreamDeclaration,
)
from proofmatch.upstream import (
    batch_declarations,
    estimate_upstream_batches,
    load_upstream_declarations,
    validate_assignments,
)


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


class UpstreamTests(unittest.TestCase):
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
