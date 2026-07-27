from __future__ import annotations

import json
import hashlib
from collections import Counter
from collections.abc import Iterable
from dataclasses import asdict
from pathlib import Path

from proofmatch.budget import StageEstimate, token_cost
from proofmatch.models import (
    DocumentBlock,
    DocumentIndex,
    ProofStepAssignment,
    ProofStepManifest,
    UpstreamDeclaration,
)


def _target_record(dataset: Path, lean_name: str) -> dict[str, object]:
    with dataset.open(encoding="utf-8") as source:
        for line_number, line in enumerate(source, start=1):
            try:
                record = json.loads(line)
            except json.JSONDecodeError as error:
                raise ValueError(
                    f"invalid JSONL record at line {line_number}"
                ) from error
            if record.get("lean_name") == lean_name or record.get("id") == lean_name:
                return record
    raise ValueError(f"{lean_name} is absent from {dataset}")


def _statement_and_excerpt(lines: list[str]) -> tuple[str, str]:
    boundary = next(
        (
            index
            for index, line in enumerate(lines)
            if ":=" in line or line.strip() == "where"
        ),
        len(lines) - 1,
    )
    statement = "\n".join(lines[: boundary + 1]).strip()
    excerpt = "\n".join(lines[boundary + 1 :]).strip()
    if not excerpt:
        excerpt = "\n".join(lines).strip()
    if len(excerpt) > 4_000:
        excerpt = excerpt[:3_976].rstrip() + "\n...[excerpt truncated]"
    return statement, excerpt


def load_upstream_declarations(
    dataset: Path,
    dependency_graph: Path,
    lean_name: str,
) -> tuple[UpstreamDeclaration, ...]:
    from scripts.build_dataset import build_index

    target = _target_record(dataset, lean_name)
    names = target.get("proof_upstream_decls")
    if not isinstance(names, list) or not names:
        raise ValueError(f"{lean_name} has no proof_upstream_decls")
    graph_value = json.loads(dependency_graph.read_text(encoding="utf-8"))
    modules = graph_value.get("modules")
    if not isinstance(modules, dict):
        raise ValueError(f"{dependency_graph} has no modules object")
    index = build_index(modules)
    declarations = []
    for position, name_value in enumerate(names):
        name = str(name_value)
        if name == lean_name:
            raise ValueError(
                f"proof_upstream_decls unexpectedly contains target {lean_name}"
            )
        record = index.get(name)
        if record is None:
            raise ValueError(
                f"proof_upstream_decls[{position}] {name} is absent "
                "from the dependency graph"
            )
        lines = [str(line) for line in record.get("slice", ())]
        statement, excerpt = _statement_and_excerpt(lines)
        declarations.append(
            UpstreamDeclaration(
                lean_name=name,
                kind=str(record.get("kind") or ""),
                statement=statement,
                source_module=str(record.get("module") or ""),
                direct_dependencies=tuple(
                    str(item) for item in record.get("all_deps", ())
                ),
                proof_excerpt=excerpt,
            )
        )
    return tuple(declarations)


def _serialized_declaration_size(declaration: UpstreamDeclaration) -> int:
    return len(
        json.dumps(
            asdict(declaration),
            ensure_ascii=False,
            sort_keys=True,
            separators=(",", ":"),
        )
    )


def batch_declarations(
    declarations: Iterable[UpstreamDeclaration],
    max_characters: int = 48_000,
) -> tuple[tuple[UpstreamDeclaration, ...], ...]:
    if max_characters < 1:
        raise ValueError("max_characters must be positive")
    batches: list[tuple[UpstreamDeclaration, ...]] = []
    current: list[UpstreamDeclaration] = []
    current_size = 0
    for declaration in declarations:
        item_size = _serialized_declaration_size(declaration)
        separator_size = 1 if current else 0
        if current and current_size + separator_size + item_size > max_characters:
            batches.append(tuple(current))
            current = []
            current_size = 0
            separator_size = 0
        current.append(declaration)
        current_size += separator_size + item_size
    if current:
        batches.append(tuple(current))
    return tuple(batches)


def estimate_upstream_batches(
    batches: Iterable[tuple[UpstreamDeclaration, ...]],
    proof_blocks: Iterable[DocumentBlock],
    model: str = "gpt-5.6-luna",
) -> tuple[StageEstimate, ...]:
    block_payload = [
        {
            "block_id": block.block_id,
            "title": block.title,
            "markdown": block.markdown,
        }
        for block in proof_blocks
    ]
    estimates = []
    for position, batch in enumerate(batches, start=1):
        payload = {
            "declarations": [asdict(item) for item in batch],
            "proof_blocks": block_payload,
        }
        characters = len(
            json.dumps(payload, ensure_ascii=False, sort_keys=True)
        )
        input_tokens = (characters + 3) // 4
        output_tokens = 160 * len(batch)
        estimates.append(
            StageEstimate(
                f"upstream mapping batch {position}",
                input_tokens,
                output_tokens,
                token_cost(model, input_tokens, output_tokens),
            )
        )
    return tuple(estimates)


def _assignment_from_json(value: object) -> ProofStepAssignment:
    if not isinstance(value, dict):
        raise ValueError("upstream assignment must be an object")
    expected = {
        "lean_name",
        "relation",
        "document_blocks",
        "rationale",
    }
    unknown = sorted(set(value) - expected)
    missing = sorted(expected - set(value))
    if unknown or missing:
        details = []
        if unknown:
            details.append(f"unexpected fields: {', '.join(unknown)}")
        if missing:
            details.append(f"missing fields: {', '.join(missing)}")
        raise ValueError("; ".join(details))
    blocks = value["document_blocks"]
    if not isinstance(blocks, list) or not all(
        isinstance(item, str) for item in blocks
    ):
        raise ValueError("document_blocks must be an array of strings")
    relation = value["relation"]
    if relation not in {"direct", "context"}:
        raise ValueError("relation must be direct or context")
    return ProofStepAssignment(
        lean_name=str(value["lean_name"]),
        relation=relation,
        document_blocks=tuple(blocks),
        rationale=str(value["rationale"]),
    )


def map_upstream_batches(
    declarations: Iterable[UpstreamDeclaration],
    proof_blocks: Iterable[DocumentBlock],
    agent,
    budget,
) -> tuple[ProofStepAssignment, ...]:
    ordered = tuple(declarations)
    blocks = tuple(proof_blocks)
    allowed_blocks = {block.block_id for block in blocks}
    batches = batch_declarations(ordered)
    estimates = estimate_upstream_batches(batches, blocks)
    assignments = []
    for batch, estimate in zip(batches, estimates, strict=True):
        budget.require(estimate)
        output = agent.run(
            "map_upstream",
            {
                "declarations": [asdict(item) for item in batch],
                "proof_blocks": [
                    {
                        "block_id": block.block_id,
                        "page": block.page,
                        "title": block.title,
                        "markdown": block.markdown,
                    }
                    for block in blocks
                ],
            },
        )
        rows = output.get("assignments")
        if not isinstance(rows, list):
            raise ValueError("agent output must contain an assignments array")
        batch_assignments = tuple(_assignment_from_json(row) for row in rows)
        assignments.extend(
            validate_assignments(batch, batch_assignments, allowed_blocks)
        )
    return validate_assignments(ordered, assignments, allowed_blocks)


def _sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def _dependency_fingerprint(
    declarations: Iterable[UpstreamDeclaration],
) -> str:
    value = [
        {
            "lean_name": declaration.lean_name,
            "kind": declaration.kind,
            "statement": declaration.statement,
            "source_module": declaration.source_module,
            "direct_dependencies": list(declaration.direct_dependencies),
            "proof_excerpt": declaration.proof_excerpt,
        }
        for declaration in declarations
    ]
    return _sha256_text(
        json.dumps(
            value,
            ensure_ascii=False,
            sort_keys=True,
            separators=(",", ":"),
        )
    )


def build_manifest(
    theorem: str,
    document: str,
    index: DocumentIndex,
    proof_text: str,
    declarations: Iterable[UpstreamDeclaration],
    assignments: Iterable[ProofStepAssignment],
) -> ProofStepManifest:
    ordered_declarations = tuple(declarations)
    return ProofStepManifest(
        theorem=theorem,
        document=document,
        source_fingerprint=index.source_fingerprint,
        proof_fingerprint=_sha256_text(proof_text),
        dependency_fingerprint=_dependency_fingerprint(ordered_declarations),
        assignments=tuple(assignments),
    )


def validate_manifest(
    manifest: ProofStepManifest,
    index: DocumentIndex,
    proof_text: str,
    declarations: Iterable[UpstreamDeclaration],
    allowed_blocks: set[str],
) -> None:
    ordered_declarations = tuple(declarations)
    if manifest.source_fingerprint != index.source_fingerprint:
        raise ValueError("validated Markdown fingerprint changed")
    if manifest.proof_fingerprint != _sha256_text(proof_text):
        raise ValueError("Lean proof fingerprint changed")
    if manifest.dependency_fingerprint != _dependency_fingerprint(
        ordered_declarations
    ):
        raise ValueError("Lean dependency fingerprint changed")
    validate_assignments(
        ordered_declarations,
        manifest.assignments,
        allowed_blocks,
    )


def render_upstream_review(
    manifest: ProofStepManifest,
    blocks_by_id: dict[str, DocumentBlock],
) -> str:
    total = len(manifest.assignments)
    direct = sum(item.relation == "direct" for item in manifest.assignments)
    contextual = total - direct
    lines = [
        f"# Upstream proof-step review: `{manifest.theorem}`",
        "",
        f"- Coverage: {total}/{total} (100%)",
        f"- Direct declarations: {direct}",
        f"- Contextual declarations: {contextual}",
        f"- Document: `{manifest.document}`",
        "",
    ]
    groups: list[list[ProofStepAssignment]] = []
    for assignment in manifest.assignments:
        if (
            groups
            and groups[-1][0].relation == assignment.relation
            and groups[-1][0].document_blocks == assignment.document_blocks
        ):
            groups[-1].append(assignment)
        else:
            groups.append([assignment])
    for group in groups:
        first = group[0]
        label = "direct" if first.relation == "direct" else "contextual"
        lines.extend(
            [
                f"## {len(group)} {label} declarations",
                "",
                "Blocks: "
                + ", ".join(f"`{block}`" for block in first.document_blocks),
                "",
            ]
        )
        for block_id in first.document_blocks:
            block = blocks_by_id.get(block_id)
            if block is not None:
                summary = " ".join(block.markdown.split())
                lines.append(f"> {summary[:240]}")
                lines.append("")
        for assignment in group:
            lines.append(
                f"- `{assignment.lean_name}` — {assignment.rationale}"
            )
        lines.append("")
    return "\n".join(lines).rstrip() + "\n"


def validate_assignments(
    declarations: Iterable[UpstreamDeclaration],
    assignments: Iterable[ProofStepAssignment],
    allowed_blocks: set[str],
) -> tuple[ProofStepAssignment, ...]:
    ordered_declarations = tuple(declarations)
    proposed = tuple(assignments)
    expected_names = [item.lean_name for item in ordered_declarations]
    proposed_names = [item.lean_name for item in proposed]
    expected_set = set(expected_names)
    counts = Counter(proposed_names)

    duplicate = sorted(name for name, count in counts.items() if count > 1)
    unknown = sorted(set(proposed_names) - expected_set)
    missing = sorted(expected_set - set(proposed_names))
    failures = []
    if duplicate:
        failures.append(f"duplicate declarations: {', '.join(duplicate)}")
    if unknown:
        failures.append(f"unknown declarations: {', '.join(unknown)}")
    if missing:
        failures.append(f"missing declarations: {', '.join(missing)}")
    if failures:
        raise ValueError("; ".join(failures))

    by_name = {item.lean_name: item for item in proposed}
    for name in expected_names:
        assignment = by_name[name]
        if assignment.relation not in {"direct", "context"}:
            raise ValueError(
                f"{name} relation must be direct or context, "
                f"got {assignment.relation!r}"
            )
        if not assignment.document_blocks:
            raise ValueError(f"{name} must cite at least one document block")
        invalid = [
            block
            for block in assignment.document_blocks
            if block not in allowed_blocks
        ]
        if invalid:
            raise ValueError(
                f"{name} cites blocks outside the allowed proof context: "
                f"{', '.join(invalid)}"
            )

    return tuple(by_name[name] for name in expected_names)
