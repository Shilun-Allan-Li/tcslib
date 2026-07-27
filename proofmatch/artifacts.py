from __future__ import annotations

import hashlib
import json
from collections.abc import Mapping
from pathlib import Path


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


class RunStore:
    def __init__(self, root: Path, source_fingerprint: str):
        if not source_fingerprint or "/" in source_fingerprint:
            raise ValueError("source_fingerprint must be a nonempty path-safe value")
        self.directory = root / source_fingerprint

    def stage_path(self, stage: str, suffix: str = ".json") -> Path:
        if not stage or "/" in stage or "\\" in stage:
            raise ValueError("stage must be a nonempty filename component")
        return self.directory / f"{stage}{suffix}"

    def write_json(self, stage: str, value: Mapping[str, object]) -> Path:
        self.directory.mkdir(parents=True, exist_ok=True)
        target = self.stage_path(stage)
        temporary = target.with_suffix(".json.tmp")
        temporary.write_text(
            json.dumps(value, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
        temporary.replace(target)
        return target

    def read_json(self, stage: str) -> dict[str, object] | None:
        target = self.stage_path(stage)
        if not target.exists():
            return None
        value = json.loads(target.read_text(encoding="utf-8"))
        if not isinstance(value, dict):
            raise ValueError(f"{target} must contain a JSON object")
        return value
