from __future__ import annotations

import json
import re
import subprocess
import time
import tempfile
from collections.abc import Mapping, Sequence
from decimal import Decimal
from pathlib import Path
from typing import Callable


Runner = Callable[..., subprocess.CompletedProcess[str]]

#: Transient-failure retry policy for `claude -p`. Three attempts total, doubling from
#: this delay. Kept small: a stuck stage should surface, not spin.
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

# Model tiers for the pipeline. DEFAULT_MODEL runs the high-volume stages
# (cleanup, relevance, upstream mapping); COMPARE_MODEL runs the heavier
# proof-structure comparison. Set DEFAULT_MODEL to "claude-sonnet-5" to get a
# cheap-tier/expensive-tier cost split; MODEL_PRICES in budget.py must have an
# entry for whatever is configured here.
DEFAULT_MODEL = "claude-opus-4-8"
COMPARE_MODEL = "claude-opus-4-8"

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


class AgentOutputError(RuntimeError):
    pass


class AgentInvocationError(AgentOutputError):
    """The claude CLI itself failed (outage, usage limit, auth) — distinct from
    a successful invocation returning malformed output."""


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

    Claude Code strips constraint keywords the structured-output API does not
    enforce (minimum, maximum, minItems, pattern), so those are re-checked here.
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


def parse_agent_output(text: str) -> dict[str, object]:
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


class ClaudeAgent:
    def __init__(
        self,
        resource_root: Path | None = None,
        runner: Runner = subprocess.run,
        model: str = DEFAULT_MODEL,
    ):
        self.resource_root = resource_root or Path(__file__).parent
        self.runner = runner
        self.model = model
        self.spent_usd = Decimal("0")

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
        sections = [prompt.rstrip()]
        if images:
            listing = "\n".join(f"- {image}" for image in images)
            sections.append(
                "Rendered PDF page images (open each with the Read tool before "
                f"answering):\n{listing}"
            )
        sections.append(
            "<untrusted-payload>\n"
            f"{json.dumps(payload, ensure_ascii=False, indent=2)}\n"
            "</untrusted-payload>"
        )
        envelope = "\n\n".join(sections) + "\n"
        # Claude Code's schema validator cannot resolve external meta-schema
        # references, so metadata keys are dropped from the CLI copy.
        cli_schema = {
            key: value
            for key, value in schema_value.items()
            if key not in ("$schema", "$id")
        }
        command = build_claude_command(
            json.dumps(cli_schema, ensure_ascii=False, separators=(",", ":")),
            images,
            self.model,
        )
        # cwd is a fresh temp dir so the invocation picks up no project
        # CLAUDE.md or settings from wherever the pipeline happens to run.
        #
        # Transient API failures are retried. Only the comparison loop degrades
        # gracefully on AgentInvocationError; routing and relevance do not, so one
        # dropped connection during `route_chapters` used to abandon a whole document
        # before any work was written (observed: "Connection closed mid-response"
        # killing a match eight minutes in, after a four-hour sibling had just
        # succeeded). Failures that will not improve on a retry -- a content-filter
        # block, a malformed schema -- are raised immediately.
        result = None
        for attempt in range(_INVOCATION_ATTEMPTS):
            with tempfile.TemporaryDirectory(prefix="proofmatch-agent-") as tmp:
                try:
                    result = self.runner(
                        command,
                        input=envelope,
                        check=True,
                        capture_output=True,
                        text=True,
                        encoding="utf-8",
                        cwd=tmp,
                    )
                    break
                except (OSError, subprocess.CalledProcessError) as error:
                    stderr = getattr(error, "stderr", "") or ""
                    stdout = getattr(error, "stdout", "") or ""
                    # The CLI reports API failures as a JSON envelope on stdout;
                    # surface its result message (e.g. content-filter blocks)
                    # instead of a truncated envelope prefix.
                    detail = ""
                    try:
                        envelope_value = json.loads(stdout)
                        if isinstance(envelope_value, dict):
                            detail = str(envelope_value.get("result") or "")
                    except json.JSONDecodeError:
                        pass
                    detail = detail or stderr.strip() or stdout.strip()[:300]
                    last = attempt == _INVOCATION_ATTEMPTS - 1
                    if last or not _is_transient(detail):
                        raise AgentInvocationError(
                            f"claude invocation failed: {detail}"
                        ) from error
                    delay = _INVOCATION_BACKOFF_SECONDS * (2 ** attempt)
                    print(
                        f"  transient agent failure ({detail[:80]}); "
                        f"retry {attempt + 1}/{_INVOCATION_ATTEMPTS - 1} in {delay}s"
                    )
                    time.sleep(delay)
        assert result is not None
        output = parse_agent_output(result.stdout)
        structured = output["structured_output"]
        assert isinstance(structured, dict)
        validate_against_schema(structured, schema_value)
        cost = output.get("total_cost_usd")
        if isinstance(cost, (int, float)):
            self.spent_usd += Decimal(str(cost))
        return structured
