import unittest

from proofmatch.compare import (
    choose_comparison_direction,
    render_difference_report,
    verdict_from_agent,
)


class CompareTests(unittest.TestCase):
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
