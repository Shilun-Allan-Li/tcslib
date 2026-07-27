from __future__ import annotations

from collections.abc import Sequence

from proofmatch.agents import CodexAgent
from proofmatch.budget import Budget, StageEstimate, token_cost
from proofmatch.models import Candidate, ComparisonVerdict, DocumentIndex


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
    if verdict not in {"same", "different", "uncertain"}:
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
    agent: CodexAgent,
    budget: Budget,
) -> ComparisonVerdict:
    selected = [
        block
        for block in document.blocks
        if not candidate.document_blocks or block.block_id in candidate.document_blocks
    ]
    pdf_tokens = sum((len(block.markdown) + 3) // 4 for block in selected)
    lean_tokens = candidate.proof_tokens + (len(candidate.formal_statement) + 3) // 4
    input_tokens = pdf_tokens + lean_tokens + 2_000
    output_tokens = 4_000
    budget.require(
        StageEstimate(
            "proof comparison",
            input_tokens,
            output_tokens,
            token_cost("gpt-5.6-terra", input_tokens, output_tokens),
        )
    )
    result = agent.run(
        "compare",
        {
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
        },
    )
    return verdict_from_agent(result)


def render_difference_report(
    verdicts: Sequence[ComparisonVerdict],
) -> str | None:
    reportable = [
        verdict for verdict in verdicts if verdict.verdict in {"different", "uncertain"}
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
