from __future__ import annotations

import json
from collections import Counter
from collections.abc import Iterable
from dataclasses import asdict
from pathlib import Path

from proofmatch.budget import StageEstimate, token_cost
from proofmatch.models import (
    DocumentBlock,
    ProofStepAssignment,
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
