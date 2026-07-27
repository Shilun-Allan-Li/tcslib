import unittest
from decimal import Decimal

from proofmatch.budget import Budget
from proofmatch.compare import (
    compare_candidate,
    choose_comparison_direction,
    render_difference_report,
    verdict_from_agent,
)
from proofmatch.models import Candidate, DocumentBlock, DocumentIndex


class CompareTests(unittest.TestCase):
    def test_comparison_rejects_prose_in_place_of_block_id(self):
        block = DocumentBlock(
            "pdf-a-p001-b001", 1, 1, "prose", "T", "text", 1
        )
        candidate = Candidate(
            "T.foo", "T", "M", "text", "True", "by trivial", 2, 1,
            (block.block_id,),
        )

        class Agent:
            def run(self, name, payload):
                return {
                    "lean_name": "T.foo",
                    "document_blocks": ["For f, the derivative is linear."],
                    "verdict": "same",
                    "confidence": 0.9,
                    "differences": [],
                    "evidence": [],
                    "pdf_outline": [],
                    "lean_outline": [],
                }

        with self.assertRaisesRegex(ValueError, "unavailable document blocks"):
            compare_candidate(
                candidate,
                DocumentIndex("abcdef123456", (block,), ()),
                Agent(),
                Budget(Decimal("1")),
            )

    def test_searches_from_shorter_side(self):
        self.assertEqual(
            choose_comparison_direction(pdf_tokens=2_000, lean_tokens=20_000),
            "pdf_to_lean",
        )
        self.assertEqual(
            choose_comparison_direction(pdf_tokens=30_000, lean_tokens=8_000),
            "lean_to_pdf",
        )

    def test_same_verdict_produces_no_difference_report(self):
        verdict = verdict_from_agent(
            {
                "lean_name": "T.foo",
                "document_blocks": ["pdf-a-p001-b001"],
                "verdict": "same",
                "confidence": 0.95,
                "differences": [],
                "evidence": ["Both use induction on n."],
                "pdf_outline": ["Induct on n."],
                "lean_outline": ["Induct on n."],
            }
        )

        self.assertIsNone(render_difference_report([verdict]))

    def test_contradictory_same_verdict_becomes_uncertain(self):
        verdict = verdict_from_agent(
            {
                "lean_name": "T.foo",
                "document_blocks": ["pdf-a-p001-b001"],
                "verdict": "same",
                "confidence": 0.7,
                "differences": ["The Lean proof uses a different induction parameter."],
                "evidence": ["outlines diverge"],
                "pdf_outline": [],
                "lean_outline": [],
            }
        )

        self.assertEqual(verdict.verdict, "uncertain")
        self.assertIn("different induction parameter", render_difference_report([verdict]))

    def test_report_contains_only_non_same_verdicts(self):
        different = verdict_from_agent(
            {
                "lean_name": "T.bar",
                "document_blocks": ["pdf-a-p001-b002"],
                "verdict": "different",
                "confidence": 0.9,
                "differences": ["Uses a counting injection instead of induction."],
                "evidence": ["PDF block 2 versus Lean have hencode."],
                "pdf_outline": [],
                "lean_outline": [],
            }
        )

        report = render_difference_report([different])

        self.assertIn("T.bar", report)
        self.assertIn("counting injection", report)


if __name__ == "__main__":
    unittest.main()
