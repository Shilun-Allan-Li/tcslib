from __future__ import annotations

from collections.abc import Sequence
from decimal import Decimal

from proofmatch.agents import DEFAULT_MODEL
from proofmatch.budget import Budget, StageEstimate, token_cost
from proofmatch.models import (
    Candidate,
    DocumentIndex,
    RelevanceDecision,
)

RELEVANCE_BATCH_SIZE = 20


def prepare_relevance_payload(
    candidates: Sequence[Candidate],
    index: DocumentIndex,
) -> dict[str, object]:
    return {
        "document_blocks": [
            {
                "block_id": block.block_id,
                "kind": block.kind,
                "title": block.title,
                "markdown": block.markdown,
            }
            for block in index.blocks
        ],
        "candidates": [
            {
                "lean_name": item.lean_name,
                "title": item.title,
                "statement": item.statement,
                "formal_statement": item.formal_statement,
                "suggested_document_blocks": list(item.document_blocks),
            }
            for item in candidates
        ]
    }


def _estimate_relevance_batch(
    candidates: Sequence[Candidate],
    index: DocumentIndex,
) -> StageEstimate:
    payload = prepare_relevance_payload(candidates, index)
    input_tokens = (len(str(payload)) + 3) // 4 + 1_000
    output_tokens = 250 * len(candidates) + 500
    return StageEstimate(
        "chapter relevance",
        input_tokens,
        output_tokens,
        token_cost(DEFAULT_MODEL, input_tokens, output_tokens),
    )


def _candidate_batches(
    candidates: Sequence[Candidate],
) -> tuple[Sequence[Candidate], ...]:
    return tuple(
        candidates[start : start + RELEVANCE_BATCH_SIZE]
        for start in range(0, len(candidates), RELEVANCE_BATCH_SIZE)
    )


def estimate_relevance(
    candidates: Sequence[Candidate],
    index: DocumentIndex,
) -> StageEstimate:
    estimates = tuple(
        _estimate_relevance_batch(batch, index)
        for batch in _candidate_batches(candidates)
    )
    return StageEstimate(
        "chapter relevance",
        sum(item.input_tokens for item in estimates),
        sum(item.output_tokens for item in estimates),
        sum((item.usd for item in estimates), start=Decimal("0")),
    )


def decisions_from_agent(
    value: dict[str, object],
    candidates: Sequence[Candidate],
    index: DocumentIndex,
) -> tuple[RelevanceDecision, ...]:
    rows = value.get("decisions")
    if not isinstance(rows, list):
        raise ValueError("relevance output must contain decisions")
    candidate_by_name = {item.lean_name: item for item in candidates}
    known_blocks = {block.block_id for block in index.blocks}
    decisions = []
    seen = set()
    for row in rows:
        if not isinstance(row, dict):
            raise ValueError("relevance decision must be an object")
        name = str(row.get("lean_name") or "")
        if name not in candidate_by_name or name in seen:
            raise ValueError(f"invalid or duplicate relevance candidate: {name}")
        seen.add(name)
        status = str(row.get("status") or "")
        if status not in {"relevant", "irrelevant", "uncertain"}:
            raise ValueError(f"invalid relevance status: {status}")
        raw_blocks = row.get("document_blocks")
        if not isinstance(raw_blocks, list) or not all(
            isinstance(item, str) for item in raw_blocks
        ):
            raise ValueError("relevance document_blocks must be strings")
        blocks = tuple(raw_blocks)
        if any(block not in known_blocks for block in blocks):
            raise ValueError("relevance decision cites unknown source block")
        if status == "irrelevant" and blocks:
            raise ValueError("irrelevant candidate must cite no blocks")
        if status != "irrelevant" and not blocks:
            raise ValueError("relevant candidate must cite source blocks")
        decisions.append(
            RelevanceDecision(
                name,
                status,  # type: ignore[arg-type]
                blocks,
                str(row.get("rationale") or ""),
            )
        )
    missing = set(candidate_by_name) - seen
    if missing:
        raise ValueError(
            "relevance output omitted candidates: " + ", ".join(sorted(missing))
        )
    order = {item.lean_name: position for position, item in enumerate(candidates)}
    return tuple(sorted(decisions, key=lambda item: order[item.lean_name]))


def requires_comparison(decision: RelevanceDecision) -> bool:
    return decision.status in {"relevant", "uncertain"}


def classify_relevance(
    candidates: Sequence[Candidate],
    index: DocumentIndex,
    agent,
    budget: Budget,
) -> tuple[RelevanceDecision, ...]:
    decisions = []
    for batch in _candidate_batches(candidates):
        budget.require(_estimate_relevance_batch(batch, index))
        output = agent.run(
            "relevance", prepare_relevance_payload(batch, index)
        )
        decisions.extend(decisions_from_agent(output, batch, index))
    return tuple(decisions)
