import unittest
from decimal import Decimal
from pathlib import Path
from unittest.mock import patch

from proofmatch.budget import Budget
from proofmatch.catalog import BlueprintBinding
from proofmatch.chapter import (
    compare_relevant_candidates,
    expand_seed_blueprint_files,
    preflight_chapter,
)
from proofmatch.models import (
    Candidate,
    ComparisonVerdict,
    DocumentBlock,
    DocumentIndex,
    RelevanceDecision,
)


class ChapterTests(unittest.TestCase):
    def test_seed_expansion_includes_every_theorem_in_selected_blueprint_file(self):
        block = DocumentBlock(
            "pdf-abcdef123456-p001-b001",
            1,
            1,
            "prose",
            "Arrow",
            "dictator correlation",
            1,
        )
        index = DocumentIndex("abcdef123456", (block,), ())
        catalog = tuple(
            Candidate(
                name, name, "M", statement, "True", "by trivial", 2, 0, ()
            )
            for name, statement in (
                ("Arrow.main", "dictator correlation"),
                ("Arrow.helper", "technical helper"),
                ("Other.noise", "dictator correlation"),
            )
        )
        bindings = {
            "Arrow.main": BlueprintBinding("Arrow.main", Path("arrow.tex")),
            "Arrow.helper": BlueprintBinding("Arrow.helper", Path("arrow.tex")),
            "Other.noise": BlueprintBinding("Other.noise", Path("other.tex")),
        }
        seeds = (
            Candidate(
                "Arrow.main",
                "Arrow.main",
                "M",
                "dictator correlation",
                "True",
                "by trivial",
                2,
                100,
                (block.block_id,),
            ),
        )

        expanded = expand_seed_blueprint_files(
            index, seeds, catalog, bindings, max_files=1
        )

        self.assertEqual(
            {item.lean_name for item in expanded},
            {"Arrow.main", "Arrow.helper"},
        )

    def test_preflight_defers_incomplete_upstream_until_relevance_is_known(self):
        block = DocumentBlock(
            "pdf-abcdef123456-p001-b001", 1, 1, "theorem", "T", "text", 1
        )
        index = DocumentIndex("abcdef123456", (block,), ())
        candidate = Candidate(
            "T.one", "T", "M", "text", "True", "by trivial", 2, 1,
            (block.block_id,),
        )
        with patch(
            "proofmatch.chapter._upstream_inputs",
            side_effect=ValueError("dependency is absent from the dependency graph"),
        ):
            estimates = preflight_chapter(
                (candidate,), index, None, None, Budget(Decimal("10"))
            )
        self.assertGreaterEqual(len(estimates), 2)

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
