"""One structured-output call to a coding-agent CLI, on either vendor.

Every LLM step of the pipeline is `Agent.run(prompt_name, payload, schema_name)`:
the prompt under proofmatch/prompts/<name>.md, the JSON payload, and the JSON
schema under proofmatch/schemas/<name>.json the answer must satisfy.  Two
backends drive it:

    claude   `claude -p --json-schema ...`   (Claude Code CLI; cost read back from
             the envelope's total_cost_usd)
    codex    `codex exec - --output-schema ...`  (OpenAI Codex CLI; token usage read
             from the --json event stream and priced with proofmatch/budget.py)

The backend is chosen per model id (proofmatch.model_policy.backend): an OpenAI id
such as gpt-5 runs on codex, anything else on claude; PROOFMATCH_BACKEND or the
`backend=` argument overrides.  Both run the model read-only in an empty temporary
directory, so no project instructions or settings leak into the call, and both
answers are re-validated here against the full schema (the CLIs enforce only a
subset of JSON Schema).
"""

from __future__ import annotations

import json
import os
import re
import shutil
import subprocess
import time
import tempfile
from collections.abc import Mapping, Sequence
from decimal import Decimal
from pathlib import Path
from typing import Callable

from proofmatch.model_policy import BACKENDS, DEFAULT_MODEL, backend as resolve_backend


Runner = Callable[..., subprocess.CompletedProcess[str]]

#: Transient-failure retry policy for a CLI invocation. Three attempts total,
#: doubling from this delay. Kept small: a stuck stage should surface, not spin.
_INVOCATION_ATTEMPTS = 3
_INVOCATION_BACKOFF_SECONDS = 5

#: Substrings marking a failure that a retry can plausibly fix. Everything else --
#: notably content-filter refusals and schema rejections -- fails fast.
_TRANSIENT_MARKERS = (
    "connection closed",
    "connection reset",
    "connection error",
    "timed out",
    "timeout",
    "overloaded",
    "rate limit",
    "429",
    "500",
    "502",
    "503",
    "504",
    "internal server error",
    "service unavailable",
    "temporarily",
    "eof occurred",
)


def _is_transient(detail: str) -> bool:
    lowered = (detail or "").casefold()
    return any(marker in lowered for marker in _TRANSIENT_MARKERS)


# `PROOFMATCH_MODEL` / `PROOFMATCH_COMPARE_MODEL` retarget every stage from the
# environment (scripts/dataset_pipeline.py sets them from --model), so the
# constants below are only the defaults. Stage floors live in model_policy.py.
COMPARE_MODEL = os.environ.get("PROOFMATCH_COMPARE_MODEL", DEFAULT_MODEL)

# Claude Code has no --sandbox flag; read-only execution is enforced by
# disallowing every mutating or network-reaching tool. Read stays available so
# the visual-validation stage can open rendered page images.
READ_ONLY_DISALLOWED_TOOLS = (
    "Bash",
    "Edit",
    "Write",
    "NotebookEdit",
    "WebFetch",
    "WebSearch",
    "Task",
)

#: Constraint keywords neither CLI enforces (Claude Code strips them; OpenAI's
#: strict structured outputs reject some of them).  They are removed from the
#: copy handed to the CLI and re-checked here on the answer.
_UNENFORCED_KEYWORDS = frozenset({
    "minimum", "maximum", "exclusiveMinimum", "exclusiveMaximum", "multipleOf",
    "minItems", "maxItems", "uniqueItems", "minLength", "maxLength", "pattern",
    "format", "default", "$schema", "$id", "examples",
})


class AgentOutputError(RuntimeError):
    pass


class AgentInvocationError(AgentOutputError):
    """The CLI itself failed (outage, usage limit, auth) — distinct from a
    successful invocation returning malformed output."""


def validate_output_schema(value: object, location: str = "$") -> None:
    if isinstance(value, dict):
        if "uniqueItems" in value:
            raise AgentOutputError(
                f"{location}.uniqueItems is unsupported by structured output"
            )
        for key, item in value.items():
            validate_output_schema(item, f"{location}.{key}")
    elif isinstance(value, list):
        for index, item in enumerate(value):
            validate_output_schema(item, f"{location}[{index}]")


_TYPE_CHECKS: dict[str, Callable[[object], bool]] = {
    "object": lambda v: isinstance(v, dict),
    "array": lambda v: isinstance(v, list),
    "string": lambda v: isinstance(v, str),
    "integer": lambda v: isinstance(v, int) and not isinstance(v, bool),
    "number": lambda v: isinstance(v, (int, float)) and not isinstance(v, bool),
    "boolean": lambda v: isinstance(v, bool),
    "null": lambda v: v is None,
}


def validate_against_schema(
    value: object,
    schema: Mapping[str, object],
    location: str = "$",
) -> None:
    """Check the agent's answer against the full schema.

    The CLIs strip or reject constraint keywords the structured-output APIs do
    not enforce (minimum, maximum, minItems, pattern), so those are re-checked here.
    """
    type_name = schema.get("type")
    if type_name is not None:
        names = type_name if isinstance(type_name, list) else [type_name]
        if not any(_TYPE_CHECKS[name](value) for name in names):
            raise AgentOutputError(f"{location} is not of type {type_name}")
    if "enum" in schema and value not in schema["enum"]:
        raise AgentOutputError(f"{location} is not one of {schema['enum']}")
    if "const" in schema and value != schema["const"]:
        raise AgentOutputError(f"{location} is not the constant {schema['const']}")
    if isinstance(value, (int, float)) and not isinstance(value, bool):
        minimum = schema.get("minimum")
        if isinstance(minimum, (int, float)) and value < minimum:
            raise AgentOutputError(f"{location} is below the minimum {minimum}")
        maximum = schema.get("maximum")
        if isinstance(maximum, (int, float)) and value > maximum:
            raise AgentOutputError(f"{location} is above the maximum {maximum}")
    if isinstance(value, str):
        pattern = schema.get("pattern")
        if isinstance(pattern, str) and re.search(pattern, value) is None:
            raise AgentOutputError(f"{location} does not match pattern {pattern!r}")
        # The Claude CLI accepted a `"proof": "placeholder"` against minLength 20
        # (2026-10-20), so string lengths are re-checked here as the numeric bounds are.
        min_length = schema.get("minLength")
        if isinstance(min_length, int) and len(value) < min_length:
            raise AgentOutputError(f"{location} is shorter than minLength {min_length}")
        max_length = schema.get("maxLength")
        if isinstance(max_length, int) and len(value) > max_length:
            raise AgentOutputError(f"{location} is longer than maxLength {max_length}")
    if isinstance(value, dict):
        properties = schema.get("properties")
        properties = properties if isinstance(properties, dict) else {}
        required = schema.get("required")
        if isinstance(required, list):
            for name in required:
                if name not in value:
                    raise AgentOutputError(f"{location}.{name} is required but missing")
        if schema.get("additionalProperties") is False:
            unknown = sorted(set(value) - set(properties))
            if unknown:
                raise AgentOutputError(
                    f"{location} has unexpected properties: {', '.join(unknown)}"
                )
        for name, item in value.items():
            subschema = properties.get(name)
            if isinstance(subschema, Mapping):
                validate_against_schema(item, subschema, f"{location}.{name}")
    if isinstance(value, list):
        min_items = schema.get("minItems")
        if isinstance(min_items, int) and len(value) < min_items:
            raise AgentOutputError(f"{location} has fewer than {min_items} items")
        items = schema.get("items")
        if isinstance(items, Mapping):
            for index, item in enumerate(value):
                validate_against_schema(item, items, f"{location}[{index}]")


# --------------------------------------------------------------------------- #
# Schema copies for the CLIs
# --------------------------------------------------------------------------- #
def cli_schema(schema: object) -> object:
    """The schema without the keywords the CLIs do not enforce (checked here instead)."""
    if isinstance(schema, dict):
        return {k: cli_schema(v) for k, v in schema.items() if k not in _UNENFORCED_KEYWORDS}
    if isinstance(schema, list):
        return [cli_schema(v) for v in schema]
    return schema


def strict_schema(schema: object) -> object:
    """OpenAI strict structured outputs: every property required and no additional
    ones.  An optional property is made required-but-nullable; `strip_optional_nulls`
    removes the nulls afterwards so the answer matches the original schema."""
    if isinstance(schema, dict):
        out = {k: strict_schema(v) for k, v in schema.items()}
        props = out.get("properties")
        if isinstance(props, dict):
            required = set(out.get("required") or [])
            for name, sub in props.items():
                if name not in required and isinstance(sub, dict):
                    t = sub.get("type")
                    if t is None:
                        sub["type"] = ["null"]
                    elif isinstance(t, list):
                        if "null" not in t:
                            sub["type"] = [*t, "null"]
                    elif t != "null":
                        sub["type"] = [t, "null"]
            out["required"] = list(props)
            out["additionalProperties"] = False
        return out
    if isinstance(schema, list):
        return [strict_schema(v) for v in schema]
    return schema


def strip_optional_nulls(value: object, schema: Mapping[str, object]) -> object:
    """Drop `null` values of properties the original schema does not require."""
    if isinstance(value, dict):
        props = schema.get("properties")
        props = props if isinstance(props, dict) else {}
        required = set(schema.get("required") or [])
        out = {}
        for name, item in value.items():
            if item is None and name in props and name not in required:
                continue
            sub = props.get(name)
            out[name] = strip_optional_nulls(item, sub) if isinstance(sub, Mapping) else item
        return out
    if isinstance(value, list):
        items = schema.get("items")
        if isinstance(items, Mapping):
            return [strip_optional_nulls(v, items) for v in value]
    return value


# --------------------------------------------------------------------------- #
# Commands
# --------------------------------------------------------------------------- #
def build_claude_command(
    schema_json: str,
    images: Sequence[Path] = (),
    model: str = DEFAULT_MODEL,
) -> list[str]:
    command = [
        "claude",
        "-p",
        "--model",
        model,
        "--output-format",
        "json",
        "--json-schema",
        schema_json,
        "--no-session-persistence",
        "--disallowedTools",
        *READ_ONLY_DISALLOWED_TOOLS,
    ]
    if images:
        command.extend(["--allowedTools", "Read"])
        for directory in sorted({str(image.parent) for image in images}):
            command.extend(["--add-dir", directory])
    return command


def build_codex_command(
    schema_path: Path,
    last_message_path: Path,
    images: Sequence[Path] = (),
    model: str = DEFAULT_MODEL,
) -> list[str]:
    """`codex exec` reading the prompt from stdin (`-`), answering in the schema's
    shape, read-only, without a saved session, with token usage on stdout as JSONL."""
    command = [
        "codex",
        "exec",
        "--model",
        model,
        "--output-schema",
        str(schema_path),
        "--output-last-message",
        str(last_message_path),
        "--ephemeral",
        "--sandbox",
        "read-only",
        "--skip-git-repo-check",
        "--color",
        "never",
        "--json",
    ]
    for image in images:
        command.extend(["--image", str(image)])
    command.append("-")
    return command


def parse_agent_output(text: str) -> dict[str, object]:
    """The `claude -p --output-format json` envelope, checked for an error and a
    structured answer."""
    try:
        envelope = json.loads(text)
    except json.JSONDecodeError as error:
        raise AgentOutputError(f"claude output was not valid JSON: {error}") from error
    if not isinstance(envelope, dict):
        raise AgentOutputError("claude output must be a JSON object")
    if envelope.get("is_error"):
        raise AgentOutputError(f"claude reported an error: {envelope.get('result')!r}")
    if not isinstance(envelope.get("structured_output"), dict):
        raise AgentOutputError(
            "claude output lacks a structured_output object; "
            f"subtype={envelope.get('subtype')!r}"
        )
    return envelope


def parse_codex_events(text: str) -> tuple[dict[str, int], str | None, str | None]:
    """(token usage, last agent message, error) from a `codex exec --json` stream.

    The event names are matched loosely (any object carrying a `usage` with token
    counts; any `item` of type `agent_message`; any `error`/`turn.failed`), so a
    renamed event in a newer CLI degrades to a missing cost, not a failed call."""
    usage: dict[str, int] = {}
    message: str | None = None
    error: str | None = None

    def visit(node: object) -> None:
        nonlocal message, error
        if not isinstance(node, dict):
            if isinstance(node, list):
                for item in node:
                    visit(item)
            return
        u = node.get("usage")
        if isinstance(u, dict) and any(k.endswith("_tokens") for k in u):
            for key, val in u.items():
                if isinstance(val, int):
                    usage[key] = usage.get(key, 0) + val
        if node.get("type") == "agent_message" and isinstance(node.get("text"), str):
            message = node["text"]
        kind = str(node.get("type") or "")
        if kind in ("error", "turn.failed") or kind.endswith(".failed"):
            detail = node.get("message") or node.get("error") or node
            error = detail if isinstance(detail, str) else json.dumps(detail)[:300]
        for val in node.values():
            if isinstance(val, (dict, list)):
                visit(val)

    for line in text.splitlines():
        line = line.strip()
        if not line.startswith("{"):
            continue
        try:
            visit(json.loads(line))
        except json.JSONDecodeError:
            continue
    return usage, message, error


def _json_object_in(text: str) -> dict[str, object]:
    """The answer as a JSON object: the whole text, or the first {...} block in it
    (a model occasionally wraps the object in a code fence)."""
    text = text.strip()
    try:
        value = json.loads(text)
    except json.JSONDecodeError:
        start, end = text.find("{"), text.rfind("}")
        if start < 0 or end <= start:
            raise AgentOutputError(f"codex answer is not JSON: {text[:200]!r}") from None
        try:
            value = json.loads(text[start : end + 1])
        except json.JSONDecodeError as error:
            raise AgentOutputError(f"codex answer is not valid JSON: {error}") from error
    if not isinstance(value, dict):
        raise AgentOutputError("codex answer must be a JSON object")
    return value


def cli_available(name: str) -> str | None:
    """Path of the backend's executable, or None."""
    return shutil.which({"claude": "claude", "codex": "codex"}[name])


# --------------------------------------------------------------------------- #
# The agent
# --------------------------------------------------------------------------- #
class Agent:
    """One structured call per `run`; `spent_usd` accumulates across calls."""

    def __init__(
        self,
        resource_root: Path | None = None,
        runner: Runner = subprocess.run,
        model: str = DEFAULT_MODEL,
        backend: str | None = None,
    ):
        self.resource_root = resource_root or Path(__file__).parent
        self.runner = runner
        self.model = model
        self.backend = resolve_backend(model, backend)
        if self.backend not in BACKENDS:
            raise ValueError(f"unknown backend {self.backend!r}")
        self.spent_usd = Decimal("0")

    # -- prompt assembly ---------------------------------------------------- #
    def _envelope(self, prompt: str, payload: Mapping[str, object], images: Sequence[Path]) -> str:
        sections = [prompt.rstrip()]
        if images:
            listing = "\n".join(f"- {image}" for image in images)
            if self.backend == "claude":
                sections.append(
                    "Rendered PDF page images (open each with the Read tool before "
                    f"answering):\n{listing}"
                )
            else:
                sections.append(
                    "Rendered PDF page images are attached to this message, in this "
                    f"order:\n{listing}"
                )
        sections.append(
            "<untrusted-payload>\n"
            f"{json.dumps(payload, ensure_ascii=False, indent=2)}\n"
            "</untrusted-payload>"
        )
        if self.backend == "codex":
            sections.append(
                "Answer with a single JSON object matching the output schema and "
                "nothing else."
            )
        return "\n\n".join(sections) + "\n"

    # -- one invocation, with retries --------------------------------------- #
    def _invoke(self, command: list[str], stdin: str, cwd: str) -> subprocess.CompletedProcess[str]:
        last_error: Exception | None = None
        for attempt in range(_INVOCATION_ATTEMPTS):
            try:
                return self.runner(
                    command,
                    input=stdin,
                    check=True,
                    capture_output=True,
                    text=True,
                    encoding="utf-8",
                    cwd=cwd,
                )
            except (OSError, subprocess.CalledProcessError) as error:
                last_error = error
                stderr = getattr(error, "stderr", "") or ""
                stdout = getattr(error, "stdout", "") or ""
                detail = ""
                if isinstance(error, OSError) and not isinstance(error, subprocess.CalledProcessError):
                    detail = (f"cannot run `{command[0]}`: {error}.  Install the "
                              f"{self.backend} CLI and log in (python3 scripts/dataset_pipeline.py "
                              f"--check-env)")
                    raise AgentInvocationError(detail) from error
                if self.backend == "claude":
                    # The CLI reports API failures as a JSON envelope on stdout;
                    # surface its result message (e.g. content-filter blocks)
                    # instead of a truncated envelope prefix.
                    try:
                        envelope_value = json.loads(stdout)
                        if isinstance(envelope_value, dict):
                            detail = str(envelope_value.get("result") or "")
                    except json.JSONDecodeError:
                        pass
                else:
                    _, _, event_error = parse_codex_events(stdout)
                    detail = event_error or ""
                detail = detail or stderr.strip()[-600:] or stdout.strip()[:300]
                last = attempt == _INVOCATION_ATTEMPTS - 1
                if last or not _is_transient(detail):
                    raise AgentInvocationError(
                        f"{self.backend} invocation failed: {detail}"
                    ) from error
                delay = _INVOCATION_BACKOFF_SECONDS * (2 ** attempt)
                print(
                    f"  transient agent failure ({detail[:80]}); "
                    f"retry {attempt + 1}/{_INVOCATION_ATTEMPTS - 1} in {delay}s"
                )
                time.sleep(delay)
        raise AgentInvocationError(f"{self.backend} invocation failed: {last_error}")

    # -- the call ------------------------------------------------------------ #
    def run(
        self,
        prompt_name: str,
        payload: Mapping[str, object],
        schema_name: str | None = None,
        images: Sequence[Path] = (),
    ) -> dict[str, object]:
        schema_name = schema_name or prompt_name
        prompt_path = self.resource_root / "prompts" / f"{prompt_name}.md"
        schema_path = self.resource_root / "schemas" / f"{schema_name}.json"
        prompt = prompt_path.read_text(encoding="utf-8")
        try:
            schema_value = json.loads(schema_path.read_text(encoding="utf-8"))
        except json.JSONDecodeError as error:
            raise AgentOutputError(f"{schema_path} is not valid JSON: {error}") from error
        validate_output_schema(schema_value)
        envelope = self._envelope(prompt, payload, images)
        # Transient API failures are retried. Only the comparison loop degrades
        # gracefully on AgentInvocationError; routing and relevance do not, so one
        # dropped connection during `route_chapters` used to abandon a whole document
        # before any work was written.  Failures that will not improve on a retry --
        # a content-filter block, a malformed schema -- are raised immediately.
        #
        # cwd is a fresh temp dir so the invocation picks up no project
        # CLAUDE.md / AGENTS.md or settings from wherever the pipeline happens to run.
        with tempfile.TemporaryDirectory(prefix="proofmatch-agent-") as tmp:
            if self.backend == "claude":
                command = build_claude_command(
                    json.dumps(cli_schema(schema_value), ensure_ascii=False, separators=(",", ":")),
                    images,
                    self.model,
                )
                result = self._invoke(command, envelope, tmp)
                output = parse_agent_output(result.stdout)
                structured = output["structured_output"]
                assert isinstance(structured, dict)
                cost = output.get("total_cost_usd")
                if isinstance(cost, (int, float)):
                    self.spent_usd += Decimal(str(cost))
            else:
                schema_file = Path(tmp) / "schema.json"
                last_message = Path(tmp) / "answer.json"
                schema_file.write_text(
                    json.dumps(strict_schema(cli_schema(schema_value)), ensure_ascii=False),
                    encoding="utf-8",
                )
                command = build_codex_command(schema_file, last_message, images, self.model)
                result = self._invoke(command, envelope, tmp)
                usage, message, event_error = parse_codex_events(result.stdout)
                if event_error:
                    raise AgentInvocationError(f"codex reported an error: {event_error}")
                text = (last_message.read_text(encoding="utf-8") if last_message.exists()
                        else (message or ""))
                if not text.strip():
                    raise AgentOutputError("codex produced no final message")
                structured = strip_optional_nulls(_json_object_in(text), schema_value)
                assert isinstance(structured, dict)
                self.spent_usd += _codex_cost(self.model, usage)
        validate_against_schema(structured, schema_value)
        return structured


def _codex_cost(model: str, usage: Mapping[str, int]) -> Decimal:
    """Price the reported token usage (the Codex CLI reports tokens, not dollars)."""
    if not usage:
        return Decimal("0")
    from proofmatch.budget import token_cost  # lazy: budget imports model_policy

    inputs = int(usage.get("input_tokens", 0))
    cached = int(usage.get("cached_input_tokens", 0))
    outputs = int(usage.get("output_tokens", 0))
    # Cached input is billed at a fraction of the input rate; count it at 10%.
    billable_inputs = max(0, inputs - cached) + cached // 10
    return token_cost(model, billable_inputs, outputs)


#: The historical name; every caller still works, on either backend.
ClaudeAgent = Agent
