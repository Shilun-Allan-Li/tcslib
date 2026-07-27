from __future__ import annotations

import json
import math
import re
from collections import Counter
from pathlib import Path

from proofmatch.models import Candidate, DocumentIndex


TOKEN_RE = re.compile(r"[^\W_]+", re.UNICODE)
CAMEL_RE = re.compile(r"(?<=[a-z0-9])(?=[A-Z])")
STOPWORDS = {
    "a", "an", "and", "as", "at", "be", "by", "for", "from", "has", "if",
    "in", "is", "it", "of", "on", "or", "that", "the", "then", "to", "under",
    "we", "with",
}


def _tokens(text: str) -> list[str]:
    expanded = CAMEL_RE.sub(" ", text.replace("_", " ").replace(".", " "))
    return [
        token.casefold()
        for token in TOKEN_RE.findall(expanded)
        if len(token) > 1 and token.casefold() not in STOPWORDS
    ]


def _query(index: DocumentIndex) -> tuple[Counter[str], set[str]]:
    body = "\n".join(f"{block.title}\n{block.markdown}" for block in index.blocks)
    terms = Counter(_tokens(body))
    title_terms = {
        token
        for block in index.blocks
        for token in _tokens(block.title)
    }
    return terms, title_terms


def _score(
    query_terms: Counter[str],
    title_terms: set[str],
    record: dict[str, object],
) -> float:
    lean_name = str(record.get("lean_name") or record.get("id") or "")
    title = str(record.get("title") or "")
    statement = str(
        record.get("statement_informal")
        or record.get("informal_statement")
        or ""
    )
    name_counts = Counter(_tokens(lean_name))
    title_counts = Counter(_tokens(title))
    body_counts = Counter(_tokens(statement))
    score = 0.0
    for term, query_frequency in query_terms.items():
        saturation = min(query_frequency, 3)
        score += saturation * (
            5.0 * min(name_counts[term], 1)
            + 4.0 * min(title_counts[term], 1)
            + min(body_counts[term], 3) / 3.0
        )
        if term in title_terms and (name_counts[term] or title_counts[term]):
            score += 3.0
    candidate_length = sum(body_counts.values())
    if candidate_length:
        score /= 1.0 + 0.05 * math.log1p(candidate_length)
    return score


def search_candidates(
    index: DocumentIndex,
    dataset: Path,
    limit: int = 12,
) -> tuple[Candidate, ...]:
    if limit < 1:
        raise ValueError("limit must be positive")
    query_terms, title_terms = _query(index)
    candidates: list[Candidate] = []
    with dataset.open(encoding="utf-8") as source:
        for line_number, line in enumerate(source, start=1):
            try:
                record = json.loads(line)
            except json.JSONDecodeError as error:
                raise ValueError(f"invalid JSONL record at line {line_number}") from error
            score = _score(query_terms, title_terms, record)
            proof = str(record.get("proof") or "")
            statement = str(
                record.get("statement_informal")
                or record.get("informal_statement")
                or ""
            )
            candidates.append(
                Candidate(
                    lean_name=str(record.get("lean_name") or record.get("id") or ""),
                    title=str(record.get("title") or ""),
                    source_module=str(record.get("source_module") or ""),
                    statement=statement,
                    formal_statement=str(record.get("formal_statement") or ""),
                    proof=proof,
                    proof_tokens=(len(proof) + 3) // 4,
                    score=score,
                    document_blocks=tuple(block.block_id for block in index.blocks),
                )
            )
    candidates.sort(key=lambda candidate: (-candidate.score, candidate.lean_name))
    return tuple(candidates[:limit])


def prepare_rerank_payload(
    candidates: tuple[Candidate, ...] | list[Candidate],
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
                "lean_name": candidate.lean_name,
                "title": candidate.title,
                "source_module": candidate.source_module,
                "statement": candidate.statement,
                "formal_statement": candidate.formal_statement,
                "proof_tokens": candidate.proof_tokens,
                "lexical_score": candidate.score,
            }
            for candidate in candidates
        ],
    }
