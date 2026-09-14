r"""The regenerated-statement cache.

`scripts/build_informal_statements.py` writes it, `scripts/blueprint_restate.py`
reads it back into the blueprint.  The two need the same notion of "is this
entry still valid", so it lives here rather than in either script.

One JSON file per declaration under `blueprint/src/references/statements/`,
alongside the `informalized/` notes that `build_proof_notes.py` consumes.  The
key is a hash of the *formal* statement, so editing the Lean invalidates the
prose written for it and a re-run regenerates exactly those declarations.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path

BASE = Path(__file__).resolve().parent.parent
CACHE_DIR = BASE / "blueprint" / "src" / "references" / "statements"

#: Bumping this invalidates every cached statement.  Raise it whenever the
#: prompt changes in a way that should change the prose.
PROMPT_VERSION = "1"


def cache_key(formal_statement: str) -> str:
    payload = f"{PROMPT_VERSION}\0{formal_statement}"
    return hashlib.sha256(payload.encode("utf-8")).hexdigest()[:16]


def cache_path(lean_name: str, root: Path | None = None) -> Path:
    #: Lean names contain no path separator; only length needs taming.
    stem = lean_name if len(lean_name) <= 120 else (
        lean_name[:100] + "-" + hashlib.sha256(lean_name.encode()).hexdigest()[:12]
    )
    return (root or CACHE_DIR) / f"{stem}.json"


def load(lean_name: str, formal_statement: str | None = None,
         root: Path | None = None) -> dict | None:
    """The cached statement, or None when absent or stale.

    With `formal_statement` given the key is checked, so a declaration whose
    Lean statement changed since the pass ran reads as absent rather than
    silently supplying prose written for the old statement.
    """
    path = cache_path(lean_name, root)
    if not path.exists():
        return None
    try:
        entry = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError:
        return None
    if formal_statement is not None and entry.get("key") != cache_key(formal_statement):
        return None
    return entry


def load_all(root: Path | None = None) -> dict[str, dict]:
    """Every cached statement by lean_name, without key checking."""
    directory = root or CACHE_DIR
    if not directory.is_dir():
        return {}
    out: dict[str, dict] = {}
    for path in sorted(directory.glob("*.json")):
        try:
            entry = json.loads(path.read_text(encoding="utf-8"))
        except json.JSONDecodeError:
            continue
        name = entry.get("lean_name")
        if name:
            out[name] = entry
    return out
