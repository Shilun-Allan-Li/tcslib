import unittest

from proofmatch.models import ProofStepAssignment, UpstreamDeclaration
from proofmatch.upstream import validate_assignments


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
