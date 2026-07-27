from __future__ import annotations

import json
import subprocess
import tempfile
from collections.abc import Mapping, Sequence
from pathlib import Path
from typing import Callable


Runner = Callable[..., subprocess.CompletedProcess[str]]


class AgentOutputError(RuntimeError):
    pass


def validate_codex_schema(value: object, location: str = "$") -> None:
    if isinstance(value, dict):
        if "uniqueItems" in value:
            raise AgentOutputError(
                f"{location}.uniqueItems is unsupported by Codex structured output"
            )
        for key, item in value.items():
            validate_codex_schema(item, f"{location}.{key}")
    elif isinstance(value, list):
        for index, item in enumerate(value):
            validate_codex_schema(item, f"{location}[{index}]")


def build_codex_command(
    schema: Path,
    output: Path,
    images: Sequence[Path] = (),
    model: str = "gpt-5.6-luna",
) -> list[str]:
    command = [
        "codex",
        "exec",
        "--ephemeral",
        "--sandbox",
        "read-only",
        "--model",
        model,
        "--output-schema",
        str(schema),
        "--output-last-message",
        str(output),
    ]
    for image in images:
        command.extend(["--image", str(image)])
    command.append("-")
    return command


def parse_agent_output(text: str) -> dict[str, object]:
    try:
        value = json.loads(text)
    except json.JSONDecodeError as error:
        raise AgentOutputError(f"Codex final message was not valid JSON: {error}") from error
    if not isinstance(value, dict):
        raise AgentOutputError("Codex final message must be a JSON object")
    return value


class CodexAgent:
    def __init__(
        self,
        resource_root: Path | None = None,
        runner: Runner = subprocess.run,
        model: str = "gpt-5.6-luna",
    ):
        self.resource_root = resource_root or Path(__file__).parent
        self.runner = runner
        self.model = model

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
        validate_codex_schema(schema_value)
        envelope = (
            f"{prompt.rstrip()}\n\n"
            "<untrusted-payload>\n"
            f"{json.dumps(payload, ensure_ascii=False, indent=2)}\n"
            "</untrusted-payload>\n"
        )
        with tempfile.TemporaryDirectory(prefix="proofmatch-agent-") as tmp:
            output_path = Path(tmp) / "answer.json"
            command = build_codex_command(
                schema_path,
                output_path,
                images,
                self.model,
            )
            try:
                result = self.runner(
                    command,
                    input=envelope,
                    check=True,
                    capture_output=True,
                    text=True,
                    encoding="utf-8",
                )
            except (OSError, subprocess.CalledProcessError) as error:
                stderr = getattr(error, "stderr", "") or ""
                raise AgentOutputError(f"Codex invocation failed: {stderr.strip()}") from error
            if not output_path.exists():
                raise AgentOutputError(
                    f"Codex produced no final-message file; stdout={result.stdout!r}"
                )
            return parse_agent_output(output_path.read_text(encoding="utf-8"))
