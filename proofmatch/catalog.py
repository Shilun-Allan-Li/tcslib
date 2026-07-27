from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path
from typing import Mapping

from proofmatch.blueprint import ENV_RE, LEAN_RE
from proofmatch.models import Candidate


@dataclass(frozen=True)
class BlueprintBinding:
    lean_name: str
    tex_path: Path


def load_blueprint_bindings(
    blueprint_root: Path,
) -> dict[str, BlueprintBinding]:
    bindings: dict[str, BlueprintBinding] = {}
    for path in sorted(blueprint_root.rglob("*.tex")):
        text = path.read_text(encoding="utf-8", errors="ignore")
        for environment in ENV_RE.findall(text):
            for match in LEAN_RE.finditer(environment):
                for raw_name in match.group(1).split(","):
                    name = raw_name.strip()
                    if not name or name.startswith("["):
                        continue
                    if name in bindings:
                        raise ValueError(
                            f"{name} appears in multiple blueprint environments"
                        )
                    bindings[name] = BlueprintBinding(name, path)
    return bindings


def load_blueprint_candidates(
    dataset: Path,
    bindings: Mapping[str, BlueprintBinding],
) -> tuple[Candidate, ...]:
    candidates = []
    with dataset.open(encoding="utf-8") as source:
        for line_number, line in enumerate(source, start=1):
            try:
                record = json.loads(line)
            except json.JSONDecodeError as error:
                raise ValueError(
                    f"invalid JSONL record at line {line_number}"
                ) from error
            name = str(record.get("lean_name") or record.get("id") or "")
            if name not in bindings:
                continue
            proof = str(record.get("proof") or "")
            candidates.append(
                Candidate(
                    lean_name=name,
                    title=str(record.get("title") or ""),
                    source_module=str(record.get("source_module") or ""),
                    statement=str(
                        record.get("statement_informal")
                        or record.get("informal_statement")
                        or ""
                    ),
                    formal_statement=str(record.get("formal_statement") or ""),
                    proof=proof,
                    proof_tokens=(len(proof) + 3) // 4,
                    score=0.0,
                    document_blocks=(),
                )
            )
    return tuple(candidates)
