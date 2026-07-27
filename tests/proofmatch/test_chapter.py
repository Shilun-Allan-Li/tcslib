import unittest
from decimal import Decimal
from pathlib import Path
from unittest.mock import patch

from proofmatch.budget import Budget
from proofmatch.catalog import BlueprintBinding
from proofmatch.chapter import (
    _upstream_inputs,
    apply_theorem_proposals,
    compare_relevant_candidates,
    expand_seed_blueprint_files,
    preflight_chapter,
)
from proofmatch.blueprint import SourceProposal
from proofmatch.models import (
    Candidate,
    ComparisonVerdict,
    DocumentBlock,
    DocumentIndex,
    RelevanceDecision,
    UpstreamDeclaration,
)


class ChapterTests(unittest.TestCase):
    def test_blueprint_failure_does_not_block_other_theorems(self):
        good = SourceProposal(
            Path("good.tex"),
            "T.good",
            object(),
        )
        bad = SourceProposal(
            Path("bad.tex"),
            "T.bad",
            object(),
        )
        applied = []

        def fake_plan(proposals):
            if proposals[0].lean_name == "T.bad":
                raise ValueError("broken environment")
            return (f"mutation:{proposals[0].lean_name}",)

        with (
            patch("proofmatch.chapter.plan_blueprint_mutations", fake_plan),
            patch(
                "proofmatch.chapter.apply_blueprint_mutations",
                side_effect=lambda mutations: applied.extend(mutations),
            ),
        ):
            mutations, failures = apply_theorem_proposals(
                {"T.bad": [bad], "T.good": [good]}
            )

        self.assertEqual(mutations, ("mutation:T.good",))
        self.assertEqual(failures[0]["lean_name"], "T.bad")
        self.assertEqual(applied, ["mutation:T.good"])

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

    def test_upstream_mapping_uses_the_entire_chapter_context(self):
        first = DocumentBlock(
            "pdf-abcdef123456-p001-b001", 1, 1, "theorem", "T", "top", 1
        )
        later = DocumentBlock(
            "pdf-abcdef123456-p003-b002", 3, 2, "prose", "Helper", "used here", 1
        )
        index = DocumentIndex("abcdef123456", (first, later), ())
        candidate = Candidate(
            "T.one", "T", "M", "top", "True", "by trivial", 2, 1,
            (first.block_id,),
        )
        declaration = UpstreamDeclaration(
            "T.helper", "lemma", "helper", "M", (), "by trivial"
        )
        with (
            patch(
                "proofmatch.chapter.load_upstream_declarations",
                return_value=(declaration,),
            ),
            patch(
                "proofmatch.chapter.estimate_upstream_batches",
                return_value=(),
            ),
        ):
            _, blocks, _ = _upstream_inputs(
                candidate, index, Path("dataset"), Path("graph")
            )

        self.assertEqual(
            tuple(block.block_id for block in blocks),
            (first.block_id, later.block_id),
        )

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
