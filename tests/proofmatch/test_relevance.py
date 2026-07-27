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


if __name__ == "__main__":
    unittest.main()
