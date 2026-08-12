from __future__ import annotations

import fcntl
import os
import re
from contextlib import contextmanager
from dataclasses import dataclass
from pathlib import Path

#: Serialises blueprint mutation across processes.
#:
#: Writing a citation is a read-modify-write: `plan_source_insert` reads the .tex and
#: returns updated text, then `apply_blueprint_mutations` writes it. Two matches running
#: concurrently on documents that cite the same chapter would both read the old text and
#: the second write would silently drop the first one's citations. The lock must therefore
#: span plan *and* apply, not just the write.
#:
#: It is held only for the (fast) mutation step, never across the LLM stages, so
#: independent documents still route, judge and compare fully in parallel.
_LOCK_PATH = Path(__file__).resolve().parent.parent / ".proofmatch-work" / ".blueprint.lock"


@contextmanager
def blueprint_write_lock():
    """Hold an exclusive advisory lock for the duration of a plan+apply cycle."""
    _LOCK_PATH.parent.mkdir(parents=True, exist_ok=True)
    handle = os.open(_LOCK_PATH, os.O_RDWR | os.O_CREAT, 0o644)
    try:
        fcntl.flock(handle, fcntl.LOCK_EX)
        try:
            yield
        finally:
            fcntl.flock(handle, fcntl.LOCK_UN)
    finally:
        os.close(handle)


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
STATEMENT_SOURCE_RE = re.compile(
    r"\\statementsource\{([^}]*)\}\{([^}]*)\}",
    re.DOTALL,
)
SOURCE_MACROS = {
    "proofsource": PROOF_SOURCE_RE,
    "statementsource": STATEMENT_SOURCE_RE,
}
PROOF_STEP_RE = re.compile(
    r"\\proofstep\s*"
    r"\{([^}]*)\}\s*"
    r"\{([^}]*)\}\s*"
    r"\{([^}]*)\}\s*"
    r"\{([^}]*)\}",
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


@dataclass(frozen=True)
class ProofStep:
    lean_name: str
    relation: str
    document: str
    blocks: tuple[str, ...]

    def __post_init__(self) -> None:
        if not self.lean_name or any(
            char in self.lean_name for char in "{}\n"
        ):
            raise ValueError("proof-step Lean name must be safe and nonempty")
        if self.relation not in {"direct", "context"}:
            raise ValueError("proof-step relation must be direct or context")
        ProofSource(self.document, self.blocks)


@dataclass(frozen=True)
class SourceProposal:
    tex_path: Path
    lean_name: str
    source: ProofSource
    macro: str = "proofsource"

    def __post_init__(self):
        if self.macro not in SOURCE_MACROS:
            raise ValueError(f"unknown source macro: {self.macro}")


@dataclass(frozen=True)
class StepProposal:
    tex_path: Path
    theorem_name: str
    steps: tuple[ProofStep, ...]


@dataclass(frozen=True)
class BlueprintMutation:
    tex_path: Path
    original: str
    updated: str


def parse_proof_sources(
    tex: str,
    macro: str = "proofsource",
) -> dict[str, tuple[ProofSource, ...]]:
    source_re = SOURCE_MACROS[macro]
    result: dict[str, list[ProofSource]] = {}
    for environment in ENV_RE.findall(tex):
        bindings = [
            name.strip()
            for match in LEAN_RE.finditer(environment)
            for name in match.group(1).split(",")
            if name.strip() and not name.strip().startswith("[")
        ]
        sources = []
        for match in source_re.finditer(environment):
            blocks = tuple(
                block.strip()
                for block in match.group(2).split(",")
                if block.strip()
            )
            sources.append(ProofSource(match.group(1).strip(), blocks))
        for binding in bindings:
            result.setdefault(binding, []).extend(sources)
    return {name: tuple(sources) for name, sources in result.items()}


def parse_proof_steps(tex: str) -> dict[str, tuple[ProofStep, ...]]:
    result: dict[str, list[ProofStep]] = {}
    for environment in ENV_RE.findall(tex):
        bindings = [
            name.strip()
            for match in LEAN_RE.finditer(environment)
            for name in match.group(1).split(",")
            if name.strip() and not name.strip().startswith("[")
        ]
        steps = []
        for match in PROOF_STEP_RE.finditer(environment):
            blocks = tuple(
                block.strip()
                for block in match.group(4).split(",")
                if block.strip()
            )
            steps.append(
                ProofStep(
                    match.group(1).strip(),
                    match.group(2).strip(),
                    match.group(3).strip(),
                    blocks,
                )
            )
        for binding in bindings:
            result.setdefault(binding, []).extend(steps)
    return {name: tuple(steps) for name, steps in result.items()}


def _format_source(source: ProofSource, macro: str = "proofsource") -> str:
    if len(source.blocks) == 1:
        return f"\\{macro}{{{source.document}}}{{{source.blocks[0]}}}"
    body = ",\n  ".join(source.blocks)
    return f"\\{macro}{{{source.document}}}{{\n  {body}\n}}"


def _format_step(step: ProofStep) -> str:
    blocks = ",\n    ".join(step.blocks)
    return (
        "\\proofstep\n"
        f"  {{{step.lean_name}}}\n"
        f"  {{{step.relation}}}\n"
        f"  {{{step.document}}}\n"
        f"  {{{blocks}}}"
    )


def plan_source_insert(
    tex: str,
    lean_name: str,
    source: ProofSource,
    macro: str = "proofsource",
) -> str:
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
    existing = parse_proof_sources(environment, macro).get(lean_name, ())
    prior_blocks = {
        block
        for prior in existing
        if prior.document == source.document
        for block in prior.blocks
    }
    if prior_blocks:
        # Block order is not meaningful, so a re-run that cites the same blocks
        # in a different order — or a narrower rerun that cites a subset of them
        # — has nothing to add. Only genuinely new blocks are a real conflict.
        if set(source.blocks) <= prior_blocks:
            return tex
        label = "proof-source" if macro == "proofsource" else "statement-source"
        raise ValueError(f"{label} conflict for {lean_name}")
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
    annotation = "\n" + _format_source(source, macro)
    updated_environment = (
        environment[:insertion_at] + annotation + environment[insertion_at:]
    )
    return (
        tex[: target_match.start()]
        + updated_environment
        + tex[target_match.end() :]
    )


def plan_step_insert(tex: str, theorem_name: str, steps) -> str:
    incoming = tuple(steps)
    incoming_names = [step.lean_name for step in incoming]
    duplicates = sorted(
        name for name in set(incoming_names) if incoming_names.count(name) > 1
    )
    if duplicates:
        raise ValueError(
            f"duplicate incoming proof steps: {', '.join(duplicates)}"
        )
    target_match = None
    for match in ENV_RE.finditer(tex):
        bindings = [
            name.strip()
            for lean in LEAN_RE.finditer(match.group(0))
            for name in lean.group(1).split(",")
        ]
        if theorem_name in bindings:
            target_match = match
            break
    if target_match is None:
        raise ValueError(f"no blueprint environment binds {theorem_name}")
    environment = target_match.group(0)
    existing = parse_proof_steps(environment).get(theorem_name, ())
    existing_by_name = {}
    for step in existing:
        if step.lean_name in existing_by_name:
            raise ValueError(f"duplicate existing proof step: {step.lean_name}")
        existing_by_name[step.lean_name] = step
    missing = []
    for step in incoming:
        prior = existing_by_name.get(step.lean_name)
        if prior is None:
            missing.append(step)
        elif prior != step:
            raise ValueError(f"proof-step conflict for {step.lean_name}")
    if not missing:
        return tex
    uses_match = re.search(r"^[ \t]*\\uses\b", environment, re.MULTILINE)
    if uses_match:
        insertion_at = uses_match.start()
    else:
        source_matches = list(PROOF_SOURCE_RE.finditer(environment))
        if source_matches:
            insertion_at = source_matches[-1].end()
        else:
            lean_matches = [
                match
                for match in LEAN_RE.finditer(environment)
                if theorem_name
                in [name.strip() for name in match.group(1).split(",")]
            ]
            insertion_at = lean_matches[0].end()
    annotation = "\n" + "\n".join(
        _format_step(step) for step in missing
    ) + "\n"
    updated_environment = (
        environment[:insertion_at] + annotation + environment[insertion_at:]
    )
    return (
        tex[: target_match.start()]
        + updated_environment
        + tex[target_match.end() :]
    )


def plan_blueprint_mutations(
    proposals,
) -> tuple[BlueprintMutation, ...]:
    originals: dict[Path, str] = {}
    updates: dict[Path, str] = {}
    for proposal in proposals:
        path = proposal.tex_path
        if path not in originals:
            originals[path] = path.read_text(encoding="utf-8")
            updates[path] = originals[path]
        if isinstance(proposal, SourceProposal):
            updates[path] = plan_source_insert(
                updates[path], proposal.lean_name, proposal.source, proposal.macro
            )
        elif isinstance(proposal, StepProposal):
            updates[path] = plan_step_insert(
                updates[path], proposal.theorem_name, proposal.steps
            )
        else:
            raise TypeError(f"unknown blueprint proposal: {type(proposal)}")
    return tuple(
        BlueprintMutation(path, originals[path], updates[path])
        for path in sorted(originals)
        if originals[path] != updates[path]
    )


def apply_blueprint_mutations(
    mutations: tuple[BlueprintMutation, ...],
) -> None:
    temporary = []
    try:
        for mutation in mutations:
            path = mutation.tex_path.with_suffix(
                mutation.tex_path.suffix + ".proofmatch.tmp"
            )
            path.write_text(mutation.updated, encoding="utf-8")
            temporary.append((path, mutation.tex_path))
        for path, target in temporary:
            path.replace(target)
    finally:
        for path, _ in temporary:
            if path.exists():
                path.unlink()


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
    updated = plan_source_insert(tex, lean_name, source)
    if updated != tex:
        tex_path.write_text(updated, encoding="utf-8")


def insert_approved_steps(
    tex_path: Path,
    theorem_name: str,
    steps,
    *,
    approved: bool,
) -> None:
    if not approved:
        raise PermissionError("proof-step insertion requires explicit approval")
    tex = tex_path.read_text(encoding="utf-8")
    updated = plan_step_insert(tex, theorem_name, steps)
    if updated != tex:
        temporary = tex_path.with_suffix(tex_path.suffix + ".proofstep.tmp")
        temporary.write_text(updated, encoding="utf-8")
        temporary.replace(tex_path)
