from __future__ import annotations

import json
from dataclasses import MISSING, dataclass, fields, is_dataclass
from pathlib import Path
from types import UnionType
from typing import Any, Literal, TypeVar, Union, get_args, get_origin, get_type_hints


T = TypeVar("T")


@dataclass(frozen=True)
class ComparisonVerdict:
    lean_name: str
    document_blocks: tuple[str, ...]
    verdict: Literal["same", "different", "uncertain"]
    confidence: float
    differences: tuple[str, ...]
    evidence: tuple[str, ...]
    pdf_outline: tuple[str, ...] = ()
    lean_outline: tuple[str, ...] = ()


@dataclass(frozen=True)
class DocumentBlock:
    block_id: str
    page: int
    sequence: int
    kind: str
    title: str
    markdown: str
    confidence: float


@dataclass(frozen=True)
class DocumentAmbiguity:
    block_id: str
    reason: str
    resolved: bool


@dataclass(frozen=True)
class DocumentIndex:
    source_fingerprint: str
    blocks: tuple[DocumentBlock, ...]
    ambiguities: tuple[DocumentAmbiguity, ...]


@dataclass(frozen=True)
class Candidate:
    lean_name: str
    title: str
    source_module: str
    statement: str
    formal_statement: str
    proof: str
    proof_tokens: int
    score: float
    document_blocks: tuple[str, ...]


@dataclass(frozen=True)
class RelevanceDecision:
    lean_name: str
    status: Literal["relevant", "irrelevant", "uncertain"]
    document_blocks: tuple[str, ...]
    rationale: str


@dataclass(frozen=True)
class UpstreamDeclaration:
    lean_name: str
    kind: str
    statement: str
    source_module: str
    direct_dependencies: tuple[str, ...]
    proof_excerpt: str


@dataclass(frozen=True)
class ProofStepAssignment:
    lean_name: str
    relation: Literal["direct", "context"]
    document_blocks: tuple[str, ...]
    rationale: str


@dataclass(frozen=True)
class ProofStepManifest:
    theorem: str
    document: str
    source_fingerprint: str
    proof_fingerprint: str
    dependency_fingerprint: str
    assignments: tuple[ProofStepAssignment, ...]


def _convert(value: Any, expected: Any, location: str) -> Any:
    origin = get_origin(expected)
    args = get_args(expected)

    if origin is Literal:
        if value not in args:
            raise ValueError(f"{location} must be one of {args}, got {value!r}")
        return value
    if origin is tuple:
        if not isinstance(value, list):
            raise ValueError(f"{location} must be a JSON array")
        item_type = args[0] if args else Any
        return tuple(_convert(item, item_type, f"{location}[]") for item in value)
    if origin in (Union, UnionType):
        failures = []
        for item_type in args:
            if item_type is type(None) and value is None:
                return None
            try:
                return _convert(value, item_type, location)
            except ValueError as error:
                failures.append(str(error))
        raise ValueError(f"{location} does not match its allowed types: {failures}")
    if is_dataclass(expected):
        return _from_mapping(value, expected, location)
    if expected is Any:
        return value
    if expected is float and isinstance(value, (int, float)) and not isinstance(value, bool):
        return float(value)
    if not isinstance(value, expected):
        raise ValueError(f"{location} must be {expected.__name__}")
    return value


def _from_mapping(value: Any, cls: type[T], location: str) -> T:
    if not isinstance(value, dict):
        raise ValueError(f"{location} must be a JSON object")
    declared = {field.name: field for field in fields(cls)}
    unknown = sorted(set(value) - set(declared))
    if unknown:
        raise ValueError(f"{location} has unexpected fields: {', '.join(unknown)}")
    missing = [
        name
        for name, field in declared.items()
        if name not in value and field.default is MISSING and field.default_factory is MISSING
    ]
    if missing:
        raise ValueError(f"{location} is missing required fields: {', '.join(missing)}")

    hints = get_type_hints(cls)
    converted = {
        name: _convert(value[name], hints[name], f"{location}.{name}")
        for name in declared
        if name in value
    }
    return cls(**converted)


def load_typed(path: Path, cls: type[T]) -> T:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise ValueError(f"could not read valid JSON from {path}: {error}") from error
    return _from_mapping(value, cls, cls.__name__)
