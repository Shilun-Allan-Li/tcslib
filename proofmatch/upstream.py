from __future__ import annotations

from collections import Counter
from collections.abc import Iterable

from proofmatch.models import ProofStepAssignment, UpstreamDeclaration


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
