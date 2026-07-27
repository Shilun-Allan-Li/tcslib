import json
import unittest
from decimal import Decimal

from proofmatch.budget import Budget
from proofmatch.models import Candidate, DocumentBlock, DocumentIndex
from proofmatch.relevance import (
    classify_relevance,
    decisions_from_agent,
    prepare_relevance_payload,
    requires_comparison,
)


class FakeAgent:
    def __init__(self, output):
        self.output = output
        self.payload = None

    def run(self, name, payload):
        self.payload = payload
        return self.output


class RelevanceTests(unittest.TestCase):
    def setUp(self):
        self.block = DocumentBlock(
            "pdf-abcdef123456-p001-b001", 1, 1, "theorem", "One", "one", 1
        )
        self.index = DocumentIndex("abcdef123456", (self.block,), ())
        self.candidate = Candidate(
            "T.one", "One", "M", "one", "True", "SECRET PROOF", 3, 9, (self.block.block_id,)
        )

    def test_payload_omits_proofs(self):
        payload = prepare_relevance_payload((self.candidate,), self.index)
        self.assertNotIn("SECRET PROOF", json.dumps(payload))

    def test_unknown_block_is_rejected(self):
        output = {"decisions": [{
            "lean_name": "T.one", "status": "relevant",
            "document_blocks": ["pdf-abcdef123456-p999-b001"],
            "rationale": "match",
        }]}
        with self.assertRaisesRegex(ValueError, "unknown source block"):
            decisions_from_agent(output, (self.candidate,), self.index)

    def test_candidate_may_select_another_valid_chapter_block(self):
        other = DocumentBlock(
            "pdf-abcdef123456-p002-b001", 2, 1, "prose", "Two", "context", 2
        )
        index = DocumentIndex("abcdef123456", (self.block, other), ())
        output = {"decisions": [{
            "lean_name": "T.one", "status": "relevant",
            "document_blocks": [other.block_id],
            "rationale": "the retrieval seed was narrower than the match",
        }]}

        decision = decisions_from_agent(
            output, (self.candidate,), index
        )[0]

        self.assertEqual(decision.document_blocks, (other.block_id,))

    def test_payload_includes_chapter_blocks_once(self):
        payload = prepare_relevance_payload((self.candidate,), self.index)

        self.assertEqual(len(payload["document_blocks"]), 1)
        self.assertEqual(
            payload["candidates"][0]["suggested_document_blocks"],
            [self.block.block_id],
        )
        self.assertNotIn("document_blocks", payload["candidates"][0])

    def test_uncertain_advances_to_comparison(self):
        output = {"decisions": [{
            "lean_name": "T.one", "status": "uncertain",
            "document_blocks": [self.block.block_id], "rationale": "plausible",
        }]}
        decision = decisions_from_agent(
            output, (self.candidate,), self.index
        )[0]
        self.assertTrue(requires_comparison(decision))

    def test_classification_uses_one_budgeted_agent_call(self):
        output = {"decisions": [{
            "lean_name": "T.one", "status": "relevant",
            "document_blocks": [self.block.block_id], "rationale": "same statement",
        }]}
        agent = FakeAgent(output)
        result = classify_relevance(
            (self.candidate,), self.index, agent, Budget(Decimal("1"))
        )
        self.assertEqual(result[0].lean_name, "T.one")
        self.assertIsNotNone(agent.payload)

    def test_classification_batches_large_candidate_sets(self):
        candidates = tuple(
            Candidate(
                f"T.{index}",
                f"T {index}",
                "M",
                "one",
                "True",
                "",
                0,
                1,
                (self.block.block_id,),
            )
            for index in range(21)
        )

        class BatchAgent:
            def __init__(self):
                self.calls = 0

            def run(self, name, payload):
                self.calls += 1
                return {
                    "decisions": [
                        {
                            "lean_name": item["lean_name"],
                            "status": "relevant",
                            "document_blocks": [self_block.block_id],
                            "rationale": "match",
                        }
                        for item in payload["candidates"]
                    ]
                }

        self_block = self.block
        agent = BatchAgent()
        result = classify_relevance(
            candidates, self.index, agent, Budget(Decimal("1"))
        )

        self.assertEqual(agent.calls, 2)
        self.assertEqual(len(result), 21)


if __name__ == "__main__":
    unittest.main()
