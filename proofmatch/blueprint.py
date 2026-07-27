from __future__ import annotations

import re
from dataclasses import dataclass
from pathlib import Path


ENV_RE = re.compile(
    r"\\begin\{(?:theorem|lemma|definition|proposition|corollary|sublemma)\}"
    r".*?"
    r"\\end\{(?:theorem|lemma|definition|proposition|corollary|sublemma)\}",
    re.DOTALL,
)
LEAN_RE = re.compile(r"^\s*\\lean\{([^}]*)\}\s*$", re.MULTILINE)
PROOF_SOURCE_RE = re.compile(
    r"\\proofsource\{([^}]*)\}\{([^}]*)\}",
    re.DOTALL,
)
BLOCK_RE = re.compile(r"^pdf-[0-9a-f]{12}-p\d{3}-b\d{3}$")


@dataclass(frozen=True)
class ProofSource:
    document: str
    blocks: tuple[str, ...]

    def __post_init__(self) -> None:
        if not self.document or any(char in self.document for char in "{}\n"):
            raise ValueError("proof-source document must be a safe nonempty identifier")
        if not self.blocks:
            raise ValueError("proof source must contain at least one block")
        invalid = [block for block in self.blocks if not BLOCK_RE.fullmatch(block)]
        if invalid:
            raise ValueError(f"invalid proof-source block IDs: {invalid}")


def parse_proof_sources(tex: str) -> dict[str, tuple[ProofSource, ...]]:
    result: dict[str, list[ProofSource]] = {}
    for environment in ENV_RE.findall(tex):
        bindings = [
            name.strip()
            for match in LEAN_RE.finditer(environment)
            for name in match.group(1).split(",")
            if name.strip() and not name.strip().startswith("[")
        ]
        sources = []
        for match in PROOF_SOURCE_RE.finditer(environment):
            blocks = tuple(
                block.strip()
                for block in match.group(2).split(",")
                if block.strip()
            )
            sources.append(ProofSource(match.group(1).strip(), blocks))
        for binding in bindings:
            result.setdefault(binding, []).extend(sources)
    return {name: tuple(sources) for name, sources in result.items()}


def _format_source(source: ProofSource) -> str:
    if len(source.blocks) == 1:
        return f"\\proofsource{{{source.document}}}{{{source.blocks[0]}}}"
    body = ",\n  ".join(source.blocks)
    return f"\\proofsource{{{source.document}}}{{\n  {body}\n}}"


def insert_approved_source(
    tex_path: Path,
    lean_name: str,
    source: ProofSource,
    *,
    approved: bool,
) -> None:
    if not approved:
        raise PermissionError("proof-source insertion requires explicit approval")
    tex = tex_path.read_text(encoding="utf-8")
    target_match = None
    for match in ENV_RE.finditer(tex):
        bindings = [
            name.strip()
            for lean in LEAN_RE.finditer(match.group(0))
            for name in lean.group(1).split(",")
        ]
        if lean_name in bindings:
            target_match = match
            break
    if target_match is None:
        raise ValueError(f"no blueprint environment binds {lean_name}")
    environment = target_match.group(0)
    if source in parse_proof_sources(environment).get(lean_name, ()):
        return
    lean_match = next(
        match
        for match in LEAN_RE.finditer(environment)
        if lean_name in [name.strip() for name in match.group(1).split(",")]
    )
    insertion_at = lean_match.end()
    after_lean = environment[insertion_at:]
    leanok = re.match(r"\n[ \t]*\\leanok[ \t]*", after_lean)
    if leanok:
        insertion_at += leanok.end()
    annotation = "\n" + _format_source(source)
    updated_environment = (
        environment[:insertion_at] + annotation + environment[insertion_at:]
    )
    updated = (
        tex[: target_match.start()]
        + updated_environment
        + tex[target_match.end() :]
    )
    tex_path.write_text(updated, encoding="utf-8")
