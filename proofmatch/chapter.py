from __future__ import annotations

from collections.abc import Callable, Sequence
from dataclasses import replace

from proofmatch.budget import Budget
from proofmatch.compare import compare_candidate
from proofmatch.models import (
    Candidate,
    ComparisonVerdict,
    DocumentIndex,
    RelevanceDecision,
)
from proofmatch.relevance import requires_comparison


def compare_relevant_candidates(
    candidates: Sequence[Candidate],
    decisions: Sequence[RelevanceDecision],
    index: DocumentIndex,
    agent_factory: Callable[[], object],
    budget: Budget,
) -> tuple[ComparisonVerdict, ...]:
    candidates_by_name = {item.lean_name: item for item in candidates}
    block_order = {
        block.block_id: position for position, block in enumerate(index.blocks)
    }
    selected = [
        decision for decision in decisions if requires_comparison(decision)
    ]
    selected.sort(
        key=lambda decision: (
            min(block_order[block] for block in decision.document_blocks),
            decision.lean_name,
        )
    )
    verdicts = []
    for decision in selected:
        candidate = candidates_by_name.get(decision.lean_name)
        if candidate is None:
            raise ValueError(
                f"relevance decision has no candidate: {decision.lean_name}"
            )
        scoped = replace(candidate, document_blocks=decision.document_blocks)
        verdicts.append(
            compare_candidate(scoped, index, agent_factory(), budget)
        )
    return tuple(verdicts)
