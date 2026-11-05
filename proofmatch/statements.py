r"""The regenerated-statement cache.

`scripts/build_informal_statements.py` writes it, `scripts/blueprint_restate.py`
reads it back into the blueprint.  The two need the same notion of "is this
entry still valid", so it lives here rather than in either script.

One JSON file per declaration under `blueprint/src/references/statements/`,
alongside the `informalized/` notes that `scripts/informal_sources.py` turns into
`informal_proof`.  The
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

import re  # noqa: E402

_CONTEXT_LINE = re.compile(
    r"^\s*(import|open|set_option|universe|namespace|end|section|noncomputable section|"
    r"notation|local\s+notation|scoped\s+notation|infix|infixl|infixr|prefix|postfix|"
    r"macro|syntax|attribute|variable)\b|^\s*@\[[^\]]*\]\s*$"
)
_PROOF_START = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*(?:theorem|lemma)\b"
)
_INSTANCE_START = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|scoped\s+|local\s+)*instance\b"
)


def core_text(formal_statement: str) -> str:
    """The part of a formal statement the prose depends on.

    Imports, `open`/`set_option`/`universe` context, namespace wrappers, `variable`
    lines, standalone attribute lines and the instances the builder adds for
    typeclass resolution change whenever build_dataset.py learns to assemble a
    better standalone file, but they do not change what the statement *says*.  Keying the cache on this core keeps every
    cached statement valid across such builder changes; only an edit to the
    declaration or to a definition it uses invalidates its prose.
    """
    # Column-0 lines start blocks.  Lemma stubs (`theorem foo ... := sorry` emitted so a
    # definition's body elaborates) are context too: only the LAST theorem/lemma block
    # is the statement itself.
    blocks: list[list[str]] = []
    for line in formal_statement.splitlines():
        if not line.strip():
            continue
        if not line[:1].isspace() or not blocks:
            blocks.append([line.rstrip()])
        else:
            blocks[-1].append(line.rstrip())
    last_proof = max((i for i, b in enumerate(blocks) if _PROOF_START.match(b[0])), default=-1)
    out: set[str] = set()
    for i, block in enumerate(blocks):
        head = block[0]
        if _INSTANCE_START.match(head):
            continue
        if _PROOF_START.match(head) and i != last_proof:
            continue
        for line in block:
            if _CONTEXT_LINE.match(line):
                continue
            out.add(line)
    # Emission order follows the import DAG and changes when the builder's tie-break
    # does; the content does not, so the core is the sorted set of lines.
    return "\n".join(sorted(out))


def cache_key(formal_statement: str) -> str:
    payload = f"{PROMPT_VERSION}\0{core_text(formal_statement)}"
    return hashlib.sha256(payload.encode("utf-8")).hexdigest()[:16]


def legacy_cache_key(formal_statement: str) -> str:
    """The key as written before core_text(): a hash of the whole formal statement."""
    payload = f"{PROMPT_VERSION}\0{formal_statement}"
    return hashlib.sha256(payload.encode("utf-8")).hexdigest()[:16]


def rekey(lean_name: str, current_formal: str, historical_formals: list[str],
          root: Path | None = None, *, trust_unknown: bool = False) -> str:
    """Bring an entry keyed against an earlier build of the same statement up to date.

    Returns `valid` (already keyed to the current statement), `rekeyed` (it was
    keyed to a historical build whose core is the current core -- the key is
    rewritten), `changed` (the statement's core changed since the prose was
    written -- regenerate), `absent` (no cache entry), or `unknown` (keyed to
    something none of the historical datasets contain).  With `trust_unknown`
    such an entry is rekeyed anyway and reported as `trusted` -- the status quo
    of builds that read the cache without checking keys at all.
    """
    path = cache_path(lean_name, root)
    if not path.exists():
        return "absent"
    try:
        entry = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError:
        return "absent"
    want = cache_key(current_formal)
    if entry.get("key") == want:
        return "valid"
    for formal in historical_formals:
        if entry.get("key") in (legacy_cache_key(formal), cache_key(formal)):
            if core_text(formal) == core_text(current_formal):
                entry["key"] = want
                path.write_text(json.dumps(entry, ensure_ascii=False, indent=1) + "\n",
                                encoding="utf-8")
                return "rekeyed"
            return "changed"
    if trust_unknown:
        entry["key"] = want
        path.write_text(json.dumps(entry, ensure_ascii=False, indent=1) + "\n",
                        encoding="utf-8")
        return "trusted"
    return "unknown"


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
