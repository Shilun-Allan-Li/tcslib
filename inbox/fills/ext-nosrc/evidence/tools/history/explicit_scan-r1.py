"""Scan explicit tactic arguments for foreign TCSlib definitions, without Lean.

Run from the fill checkout, only as python3 -I evidence/tools/explicit_scan.py.
The exact full import closure and source masks come from prepare_rule10.py,
loaded by importlib from its recorded path. Optional census input supplies
actual Lean names, including generated definitions and projections.

Examples:
  python3 -I evidence/tools/explicit_scan.py final
  python3 -I evidence/tools/explicit_scan.py final --census evidence/rule10/final/logs/Census.log --out-prefix evidence/logs/explicit-scan-final-census

This is a lexical review aid, not an elaborator or proof of Rule 10. Suffix name
matching is conservative and does not resolve namespaces, local notation,
macros, binders or shadowing as Lean does. Source mode cannot enumerate generated
matchers/projections or anonymous instances; census mode improves that name
coverage. Tactic quotations/macros, escaped/Unicode names and implicit reduction
may evade the scan. Core/Mathlib definitions are outside this TCSlib-only name
registry. Whole-file seals independently test implicit definitional reduction.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess


PREP_PATH = Path("evidence/tools/prepare_rule10.py")
SPEC = importlib.util.spec_from_file_location("ext_nosrc_prepare_rule10", PREP_PATH)
assert SPEC is not None and SPEC.loader is not None
PREP = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(PREP)

IDENT = re.compile(r"(?<![A-Za-z0-9_'])[_A-Za-z][_A-Za-z0-9']*(?:\.[_A-Za-z][_A-Za-z0-9']*)*")
TACTIC = re.compile(r"\b(simp_all|simpa|simp|dsimp|rw|rwa|unfold|delta)\b")
DECL = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*"
    r"(?:(?:private|protected|noncomputable|unsafe|partial|scoped|local)\s+)*"
    r"(def|abbrev|opaque|instance)\s+([_A-Za-z][_A-Za-z0-9']*(?:\.[_A-Za-z][_A-Za-z0-9']*)*)"
)
SCOPE = re.compile(r"^\s*(namespace|section|end)(?:\s+([_A-Za-z][_A-Za-z0-9'.]*))?\s*$")


def digest(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def source_definitions(module: str, raw: bytes) -> list[dict]:
    """Recover ordinary named definitions; optional census is authoritative."""
    text = PREP.code_mask(raw.decode())
    namespace = ""
    scopes: list[str] = []
    out = []
    for number, line in enumerate(text.splitlines(), 1):
        scope = SCOPE.fullmatch(line)
        if scope:
            command, name = scope.groups()
            if command == "end":
                if scopes:
                    namespace = scopes.pop()
            else:
                scopes.append(namespace)
                if command == "namespace":
                    assert name
                    namespace = name.removeprefix("_root_.") if name.startswith("_root_.") else ".".join(x for x in (namespace, name) if x)
            continue
        match = DECL.match(line)
        if match:
            kind, name = match.groups()
            full = name.removeprefix("_root_.") if name.startswith("_root_.") else ".".join(x for x in (namespace, name) if x)
            out.append({"name": full, "home": module, "kind": kind,
                        "abbrev": kind == "abbrev", "registry": "source", "line": number})
    return out


def census_definitions(path: Path) -> list[dict]:
    out = []
    for line in path.read_text().splitlines():
        if PREP.TAG not in line:
            continue
        row = json.loads(line.split(PREP.TAG, 1)[1])
        if row.get("record") == "constant" and row.get("kind") == "def":
            out.append({**row, "registry": "census"})
    if not out:
        raise RuntimeError("census contains no definition records")
    return out


def balanced_end(text: str, start: int, left: str, right: str) -> int:
    depth = 0
    for i in range(start, len(text)):
        if text[i] == left:
            depth += 1
        elif text[i] == right:
            depth -= 1
            if depth == 0:
                return i + 1
    raise RuntimeError("unbalanced explicit tactic argument")


def explicit_arguments(masked: str) -> list[dict]:
    out = []
    for match in TACTIC.finditer(masked):
        tactic = match[1]
        pos = match.end()
        while pos < len(masked) and masked[pos].isspace():
            pos += 1
        while pos < len(masked) and masked[pos] in "!?":
            pos += 1
        while pos < len(masked):
            if masked.startswith("only", pos) and (pos + 4 == len(masked) or not masked[pos + 4].isalnum()):
                pos += 4
            elif masked[pos] == "(":
                pos = balanced_end(masked, pos, "(", ")")
            else:
                break
            while pos < len(masked) and masked[pos].isspace():
                pos += 1
        if pos < len(masked) and masked[pos] == "[":
            end = balanced_end(masked, pos, "[", "]")
            out.append({"tactic": tactic, "start": pos + 1, "end": end - 1,
                        "tactic_start": match.start(), "form": "bracket"})
        elif tactic in ("unfold", "delta"):
            end = len(masked)
            boundary = re.search(r"\n|;|<;>|\bat\b", masked[pos:])
            if boundary:
                end = pos + boundary.start()
            out.append({"tactic": tactic, "start": pos, "end": end,
                        "tactic_start": match.start(), "form": "bare"})
    return out


def suffixes(name: str) -> list[str]:
    parts = name.split(".")
    return [".".join(parts[i:]) for i in range(len(parts))]


def self_check() -> None:
    fixture = 'by\n  /- rw [Foreign.secret] /- simp [Hidden.defn] -/ -/\n  simp only [Reader.eq, ← Foreign.secret]\n  rw [\n    Other.secret_eq, Foreign.secret]\n  unfold Foreign.secret at h\n  delta Foreign.secret\n  dsimp only [Local.defn]\n  trace "simp [Not.code]"\n'
    masked = PREP.code_mask(fixture)
    args = explicit_arguments(masked)
    assert [x["tactic"] for x in args] == ["simp", "rw", "unfold", "delta", "dsimp"]
    names = [m.group() for arg in args for m in IDENT.finditer(masked[arg["start"]:arg["end"]])]
    assert names.count("Foreign.secret") == 4 and "Hidden.defn" not in names and "Not.code" not in names
    assert "secret" in suffixes("A.B.secret") and "B.secret" in suffixes("A.B.secret")


def scan(side: str, census: Path | None) -> dict:
    graph: dict = {}
    hashes: dict = {}
    modules = PREP.OWNED[:1] if side == "base" else PREP.OWNED
    closures = {module: sorted(PREP.closure(module, side, graph, hashes)) for module in modules}
    rows: dict[tuple[str, str], dict] = {}
    for module in sorted(graph):
        for row in source_definitions(module, PREP.source(module, side)):
            rows[(row["home"], row["name"])] = row
    if census:
        for row in census_definitions(census):
            if row["home"] in graph:
                rows[(row["home"], row["name"])] = row
    suffix_index: dict[str, list[dict]] = {}
    for row in rows.values():
        for suffix in suffixes(row["name"]):
            suffix_index.setdefault(suffix, []).append(row)
    findings = []
    own = []
    arguments = []
    for module in modules:
        raw = PREP.source(module, side)
        original = raw.decode()
        masked = PREP.code_mask(original)
        closure = set(closures[module])
        for arg in explicit_arguments(masked):
            row = {"module": module, "line": masked.count("\n", 0, arg["tactic_start"]) + 1,
                   "tactic": arg["tactic"], "form": arg["form"],
                   "argument": original[arg["start"]:arg["end"]]}
            arguments.append(row)
            for token in IDENT.finditer(masked[arg["start"]:arg["end"]]):
                name = token.group().removeprefix("_root_.")
                candidates = suffix_index.get(name, [])
                foreign = [r for r in candidates if r["home"] in closure]
                local = [r for r in candidates if r["home"] == module]
                position = arg["start"] + token.start()
                evidence = {**row, "token": name, "token_line": masked.count("\n", 0, position) + 1,
                            "column": position - masked.rfind("\n", 0, position) - 1}
                if foreign:
                    findings.append({**evidence, "candidates": foreign,
                                     "classification": "possible_foreign_definition_argument"})
                elif local:
                    own.append({**evidence, "candidates": local,
                                "classification": "owned_definition_argument"})
    return {"side": side, "base": PREP.BASE, "scope": modules,
            "registry": "source+census" if census else "source",
            "census": None if census is None else {"path": str(census), "sha256": digest(census.read_bytes())},
            "source_hashes": hashes, "closures": closures,
            "definition_registry": sorted(rows.values(), key=lambda r: (r["home"], r["name"])),
            "explicit_arguments": arguments, "possible_foreign_arguments": findings,
            "owned_arguments": own, "possible_foreign_count": len(findings),
            "limitations": __doc__.split("This is a lexical review aid", 1)[1].strip(),
            "self_checks": "passed", "tool_sha256": digest(Path(__file__).read_bytes()),
            "prepare_tool_sha256": digest(PREP_PATH.read_bytes())}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("side", choices=("base", "final"))
    parser.add_argument("--census", type=Path)
    parser.add_argument("--out-prefix", type=Path)
    args = parser.parse_args()
    self_check()
    prefix = args.out_prefix or Path("evidence/logs") / ("explicit-scan-" + args.side)
    result = scan(args.side, args.census)
    report = json.dumps(result, indent=2, ensure_ascii=False) + "\n"
    PREP.write_new(Path(str(prefix) + ".json"), report.encode())
    lines = [f"side={args.side} registry={result['registry']} self_checks=passed",
             f"modules={len(result['scope'])} explicit_arguments={len(result['explicit_arguments'])}",
             f"possible_foreign_definition_arguments={result['possible_foreign_count']}"]
    for row in result["possible_foreign_arguments"]:
        homes = ", ".join(x["name"] + " @ " + x["home"] for x in row["candidates"])
        lines.append(f"{row['module']}:{row['token_line']}:{row['column']}: {row['tactic']} [{row['token']}] => {homes}")
    lines += ["LIMITATIONS", "This is a lexical review aid" + result["limitations"]]
    text = "\n".join(lines) + "\n"
    PREP.write_new(Path(str(prefix) + ".log"), text.encode())
    print(text, end="")


if __name__ == "__main__":
    main()
