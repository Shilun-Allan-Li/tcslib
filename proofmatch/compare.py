from __future__ import annotations

from collections.abc import Sequence
import hashlib
import json
from pathlib import Path
from concurrent.futures import CancelledError

from proofmatch.agents import COMPARE_MODEL, ClaudeAgent
from proofmatch.budget import Budget, StageEstimate, token_cost
from proofmatch.models import Candidate, ComparisonVerdict, DocumentIndex
from proofmatch.artifacts import atomic_json


def choose_comparison_direction(
    pdf_tokens: int,
    lean_tokens: int,
) -> str:
    if pdf_tokens < 0 or lean_tokens < 0:
        raise ValueError("token counts cannot be negative")
    return "pdf_to_lean" if pdf_tokens <= lean_tokens else "lean_to_pdf"


def _string_tuple(value: object, field: str) -> tuple[str, ...]:
    if not isinstance(value, list) or not all(isinstance(item, str) for item in value):
        raise ValueError(f"{field} must be an array of strings")
    return tuple(value)


def verdict_from_agent(value: dict[str, object]) -> ComparisonVerdict:
    required = {
        "lean_name",
        "document_blocks",
        "verdict",
        "confidence",
        "differences",
        "evidence",
        "pdf_outline",
        "lean_outline",
    }
    missing = sorted(required - set(value))
    if missing:
        raise ValueError(f"comparison output missing: {', '.join(missing)}")
    verdict = str(value["verdict"])
    if verdict not in {
        "same",
        "method_divergence",
        "not_in_text",
        "different",
        "uncertain",
    }:
        raise ValueError(f"invalid comparison verdict: {verdict}")
    differences = _string_tuple(value["differences"], "differences")
    if verdict == "same" and differences:
        verdict = "uncertain"
    confidence = float(value["confidence"])
    if not 0 <= confidence <= 1:
        raise ValueError("comparison confidence must be between 0 and 1")
    return ComparisonVerdict(
        lean_name=str(value["lean_name"]),
        document_blocks=_string_tuple(value["document_blocks"], "document_blocks"),
        verdict=verdict,
        confidence=confidence,
        differences=differences,
        evidence=_string_tuple(value["evidence"], "evidence"),
        pdf_outline=_string_tuple(value["pdf_outline"], "pdf_outline"),
        lean_outline=_string_tuple(value["lean_outline"], "lean_outline"),
    )


def compare_candidate(
    candidate: Candidate,
    document: DocumentIndex,
    agent: ClaudeAgent,
    budget: Budget,
    *,
    cache_dir: Path | None = None,
    stop_event=None,
) -> ComparisonVerdict:
    if not candidate.proof.strip():
        raise ValueError(f"{candidate.lean_name}: proof comparison requires actual Lean proof text; "
                         "rebuild the matching dataset with proofs enabled")
    selected = [
        block
        for block in document.blocks
        if not candidate.document_blocks or block.block_id in candidate.document_blocks
    ]
    pdf_tokens = sum((len(block.markdown) + 3) // 4 for block in selected)
    lean_tokens = candidate.proof_tokens + (len(candidate.formal_statement) + 3) // 4
    payload = {
            "direction": choose_comparison_direction(pdf_tokens, lean_tokens),
            "document_blocks": [
                {
                    "block_id": block.block_id,
                    "kind": block.kind,
                    "title": block.title,
                    "markdown": block.markdown,
                }
                for block in selected
            ],
            "lean": {
                "lean_name": candidate.lean_name,
                "statement": candidate.formal_statement,
                "informal_statement": candidate.statement,
                "proof": candidate.proof,
            },
        }
    cache = None
    if cache_dir is not None:
        resources = getattr(agent, 'resource_root', Path(__file__).parent)
        material = json.dumps({'payload': payload, 'model': getattr(agent, 'model', COMPARE_MODEL),
                               'backend': getattr(agent, 'backend', ''),
                               'prompt': (resources / 'prompts/compare.md').read_text(),
                               'schema': (resources / 'schemas/compare.json').read_text()},
                              ensure_ascii=False, sort_keys=True)
        cache = cache_dir / (hashlib.sha256(material.encode()).hexdigest() + '.json')
    hit = cache is not None and cache.is_file()
    if hit:
        result = json.loads(cache.read_text())
    else:
        if stop_event is not None and stop_event.is_set():
            raise CancelledError('Comparison dispatch stopped after an earlier failure')
        budget.require(estimate_comparison(candidate, document))
        print(f'  compare: {candidate.lean_name} (requesting)', flush=True)
        result = agent.run('compare', payload)
    verdict = verdict_from_agent(result)
    if verdict.lean_name != candidate.lean_name:
        raise ValueError(
            f"comparison returned {verdict.lean_name} for {candidate.lean_name}"
        )
    allowed_blocks = {block.block_id for block in selected}
    invalid = [
        block
        for block in verdict.document_blocks
        if block not in allowed_blocks
    ]
    if invalid:
        raise ValueError(
            "comparison cites unavailable document blocks: "
            + ", ".join(invalid)
        )
    if not verdict.document_blocks and verdict.verdict != "not_in_text":
        raise ValueError("comparison must cite at least one document block")
    if cache is not None and not hit:
        atomic_json(cache, result)
    print(f'  compare: {candidate.lean_name} ({"cached" if hit else "saved"})', flush=True)
    return verdict


def estimate_comparison(
    candidate: Candidate,
    document: DocumentIndex,
) -> StageEstimate:
    selected = [
        block
        for block in document.blocks
        if not candidate.document_blocks or block.block_id in candidate.document_blocks
    ]
    pdf_tokens = sum((len(block.markdown) + 3) // 4 for block in selected)
    lean_tokens = candidate.proof_tokens + (len(candidate.formal_statement) + 3) // 4
    input_tokens = pdf_tokens + lean_tokens + 2_000
    output_tokens = 4_000
    return StageEstimate(
        f"proof comparison {candidate.lean_name}",
        input_tokens,
        output_tokens,
        token_cost(COMPARE_MODEL, input_tokens, output_tokens),
    )


def render_difference_report(
    verdicts: Sequence[ComparisonVerdict],
) -> str | None:
    reportable = [
        verdict
        for verdict in verdicts
        if verdict.verdict
        in {"method_divergence", "not_in_text", "different", "uncertain"}
    ]
    if not reportable:
        return None
    lines = ["# Proof differences and uncertainties", ""]
    for verdict in reportable:
        lines.extend(
            [
                f"## {verdict.lean_name}",
                "",
                f"Verdict: `{verdict.verdict}` ({verdict.confidence:.0%} confidence)",
                "",
            ]
        )
        if verdict.differences:
            lines.extend(f"- {difference}" for difference in verdict.differences)
        else:
            lines.append("- The available evidence is insufficient for a match.")
        lines.append("")
    return "\n".join(lines).rstrip() + "\n"
