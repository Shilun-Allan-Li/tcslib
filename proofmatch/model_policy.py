"""Which model each dataset-pipeline stage may run on, and which CLI drives it.

Every LLM stage of the dataset pipeline writes prose or judgements that ship in
the dataset (informal statements, proof accounts, difficulty ratings, citation
verdicts).  Those stages need a frontier-class model: a cheaper tier produces
text that passes the mechanical rubric and still misstates a hypothesis.  This
module is the single place that says so, so that `scripts/dataset_pipeline.py`
and the per-stage scripts refuse a weaker model by default instead of quietly
producing a worse dataset.

Tiers are derived from the model id's family name, for both vendors the
pipeline can drive (`claude` = Claude Code CLI, `codex` = OpenAI Codex CLI; see
proofmatch/agents.py).  Anything the table does not recognise is tier 0 and is
rejected unless the caller allows weak models.

Environment:
    PROOFMATCH_BACKEND   claude | codex | auto (default auto: inferred from the model id)
    PROOFMATCH_MODEL     the model for every stage (default: DEFAULT_MODELS[backend])
"""

from __future__ import annotations

import os
import re

BACKENDS = ("claude", "codex")

#: Default model per backend; `PROOFMATCH_MODEL` overrides both.
DEFAULT_MODELS: dict[str, str] = {
    "claude": "claude-opus-4-8",
    "codex": "gpt-5",
}

#: (regex on the lower-cased model id, tier, backend).  First match wins, so the
#: cheaper variants of a family come before the family itself.  Higher is stronger.
_FAMILIES: tuple[tuple[str, int, str], ...] = (
    # Anthropic
    (r"(^|[-_/])haiku([-_/]|$)", 1, "claude"),
    (r"(^|[-_/])sonnet([-_/]|$)", 2, "claude"),
    (r"(^|[-_/])opus([-_/]|$)", 3, "claude"),
    (r"(^|[-_/])fable([-_/]|$)", 4, "claude"),
    (r"(^|[-_/])mythos([-_/]|$)", 4, "claude"),
    # OpenAI (driven through the Codex CLI)
    (r"(^|[-_/])gpt-5(\.\d+)?(-codex)?-nano", 1, "codex"),
    (r"(^|[-_/])gpt-5(\.\d+)?(-codex)?-mini", 2, "codex"),
    (r"(^|[-_/])gpt-5(\.\d+)?(-codex)?(-max|-pro)?([-_/]|$)", 3, "codex"),
    (r"(^|[-_/])codex([-_/]|$)", 3, "codex"),
    (r"(^|[-_/])o[134]-mini([-_/]|$)", 2, "codex"),
    (r"(^|[-_/])o[134](-pro)?([-_/]|$)", 3, "codex"),
    (r"(^|[-_/])gpt-4\.1-(mini|nano)", 1, "codex"),
    (r"(^|[-_/])gpt-4(\.1|o)?([-_/]|$)", 2, "codex"),
)

#: Family name -> tier, kept for callers that print the acceptable families.
FAMILY_TIERS: dict[str, int] = {
    "haiku": 1, "sonnet": 2, "opus": 3, "fable": 4, "mythos": 4,
    "gpt-5-nano": 1, "gpt-5-mini": 2, "gpt-5": 3, "gpt-5-codex": 3, "o3": 3, "o4-mini": 2,
    "gpt-4.1": 2,
}

#: The tier a stage needs.  "prose" covers informal statements, definition
#: descriptions and proof informalizations; "judgement" covers difficulty ratings
#: and proof-comparison verdicts; "cleanup" is the OCR-repair pass over a
#: reference document, where the model mostly transcribes.
STAGE_MIN_TIER: dict[str, int] = {
    "prose": 3,
    "judgement": 3,
    "cleanup": 2,
}


def _family(model: str) -> tuple[int, str] | None:
    name = (model or "").casefold()
    for pattern, tier, backend in _FAMILIES:
        if re.search(pattern, name):
            return tier, backend
    return None


def model_tier(model: str) -> int:
    found = _family(model)
    return found[0] if found else 0


def model_backend(model: str) -> str:
    """The CLI that serves `model`: `codex` for OpenAI ids, `claude` otherwise."""
    found = _family(model)
    return found[1] if found else "claude"


def backend(model: str | None = None, explicit: str | None = None) -> str:
    """Resolve the backend: an explicit choice, then PROOFMATCH_BACKEND, then the model id."""
    choice = (explicit or os.environ.get("PROOFMATCH_BACKEND") or "auto").strip().casefold()
    if choice in BACKENDS:
        return choice
    if choice != "auto":
        raise ValueError(f"unknown backend {choice!r}; choose one of {', '.join(BACKENDS)} or auto")
    return model_backend(model or DEFAULT_MODEL)


def default_model(explicit_backend: str | None = None) -> str:
    """PROOFMATCH_MODEL, else the default of the (explicit or configured) backend."""
    env = os.environ.get("PROOFMATCH_MODEL")
    if env:
        return env
    choice = (explicit_backend or os.environ.get("PROOFMATCH_BACKEND") or "claude").strip().casefold()
    return DEFAULT_MODELS.get(choice, DEFAULT_MODELS["claude"])


#: Default model for every stage; override per run with `--model` or per stage.
DEFAULT_MODEL = default_model()


def check_model(model: str, stage_kind: str, *, allow_weak: bool = False) -> str:
    """Return `model` if it meets the stage's floor; raise otherwise.

    `stage_kind` is a key of STAGE_MIN_TIER.  With `allow_weak` the floor is
    waived and a warning string is returned instead of raising, so a caller can
    print it and continue.
    """
    floor = STAGE_MIN_TIER[stage_kind]
    tier = model_tier(model)
    if tier >= floor:
        return model
    names = [f for f, t in FAMILY_TIERS.items() if t >= floor]
    message = (
        f"model {model!r} is below the floor for {stage_kind} stages "
        f"(needs one of: {', '.join(names)})"
    )
    if allow_weak:
        return f"WARNING: {message}; continuing because --allow-weak-models was given"
    raise ValueError(message + "; pass --allow-weak-models to override")
