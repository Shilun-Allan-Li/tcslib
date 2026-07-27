import unittest
from decimal import Decimal
from unittest.mock import patch

from proofmatch.budget import Budget
from proofmatch.chapter import compare_relevant_candidates
from proofmatch.models import (
    Candidate,
    ComparisonVerdict,
    DocumentBlock,
    DocumentIndex,
    RelevanceDecision,
)


class ChapterTests(unittest.TestCase):
    def test_every_relevant_or_uncertain_candidate_is_compared(self):
        block = DocumentBlock(
            "pdf-abcdef123456-p001-b001", 1, 1, "theorem", "T", "text", 1
        )
        index = DocumentIndex("abcdef123456", (block,), ())
        candidates = tuple(
            Candidate(name, name, "M", name, "True", "by trivial", 2, 1, (block.block_id,))
            for name in ("T.one", "T.two", "T.three")
        )
        decisions = (
            RelevanceDecision("T.one", "relevant", (block.block_id,), "yes"),
            RelevanceDecision("T.two", "irrelevant", (), "no"),
            RelevanceDecision("T.three", "uncertain", (block.block_id,), "maybe"),
        )
        calls = []

        def fake_compare(candidate, document, agent, budget):
            calls.append(candidate.lean_name)
            return ComparisonVerdict(
                candidate.lean_name, candidate.document_blocks, "same", 1, (), ()
            )

        with patch("proofmatch.chapter.compare_candidate", fake_compare):
            verdicts = compare_relevant_candidates(
                candidates,
                decisions,
                index,
                lambda: object(),
                Budget(Decimal("10")),
            )
        self.assertEqual(calls, ["T.one", "T.three"])
        self.assertEqual([item.lean_name for item in verdicts], calls)


if __name__ == "__main__":
    unittest.main()
