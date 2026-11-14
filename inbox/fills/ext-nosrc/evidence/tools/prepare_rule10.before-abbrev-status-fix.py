"""Prepare ext-nosrc Rule 10 evidence; this script never starts Lean.

Run only as python3 -I evidence/tools/prepare_rule10.py ... from the fill root.

  init base
  init final
  seals base --census-log evidence/rule10/base/logs/Census.log
  seals final --census-log evidence/rule10/final/logs/Census.log

The root worker checks the modules listed in each manifest with
scripts/lean_check_tree.sh. The base snapshot must be checked before its census;
the final owned modules must be checked before the final census. All outputs
are created exclusively, so earlier attempts are preserved.

Design provenance (read as working material): Gate06 evidence-rule10-final-r1
Collect.source.txt and build_seals.py (environment ownership, all-stored axioms,
actual-name lookup, byte-preserving whole-file insertion, EOF verification), and
its tool-inputs/request_payload_adapter.py (bounded-AST request data payload).
The old campaign-specific entrypoints/pins are not executed or imported.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess


BASE = "eff2dcd0a63f0c371118a17c67b9a5dfc046f4e9"
OWNED = [
    "TCSlib.Cryptography.Randomness.Extraction",
    "TCSlib.Cryptography.Randomness.Extraction.Rejection",
    "TCSlib.Cryptography.Randomness.Extraction.Sampler",
]
EVAL = "Complexity.PolyExpr.eval"
TAG = "FILL_CENSUS "


def digest(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def write_new(path: Path, raw: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("xb") as stream:
        stream.write(raw)


def save_json(path: Path, value: object) -> None:
    write_new(path, (json.dumps(value, indent=2, ensure_ascii=False) + "\n").encode())


def code_mask(text: str) -> str:
    """Blank nested comments and strings without changing character positions."""
    out = list(text)
    i, depth = 0, 0

    def blank(a: int, b: int) -> None:
        for j in range(a, b):
            if out[j] not in "\r\n":
                out[j] = " "

    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                blank(i, i + 2)
                depth, i = depth + 1, i + 2
            elif text.startswith("-/", i):
                blank(i, i + 2)
                depth, i = depth - 1, i + 2
            else:
                blank(i, i + 1)
                i += 1
        elif text.startswith("/-", i):
            blank(i, i + 2)
            depth, i = 1, i + 2
        elif text.startswith("--", i):
            end = text.find("\n", i)
            end = len(text) if end < 0 else end
            blank(i, end)
            i = end
        elif text[i] == "r" and (raw := re.match(r'r(#+)?"', text[i:])):
            fence = '"' + (raw.group(1) or "")
            end = text.find(fence, i + len(raw.group(0)))
            if end < 0:
                raise RuntimeError("unterminated raw source string")
            end += len(fence)
            blank(i, end)
            i = end
        elif text[i] == '"':
            end = i + 1
            while end < len(text) and text[end] != '"':
                end += 2 if text[end] == "\\" else 1
            if end >= len(text):
                raise RuntimeError("unterminated source string")
            blank(i, end + 1)
            i = end + 1
        else:
            i += 1
    if depth:
        raise RuntimeError("unterminated source comment")
    return "".join(out)


def header(raw: bytes) -> dict:
    text = raw.decode()
    masked = code_mask(text)
    offset, closed = 0, False
    first, last, imports = None, None, []
    for line in masked.splitlines(keepends=True):
        active = line.strip()
        if active:
            match = re.fullmatch(r"import\s+([A-Za-z_][A-Za-z0-9_'.]*(?:\s+[A-Za-z_][A-Za-z0-9_'.]*)*)", active)
            if match:
                if closed:
                    raise RuntimeError("import after non-import command")
                if first is None:
                    first = offset
                last = offset + len(line)
                imports.extend(match[1].split())
            else:
                if re.match(r"(?:prelude|(?:public|meta)\s+import)\b", active):
                    raise RuntimeError("unsupported import/prelude layout")
                closed = True
        offset += len(line)
    if first is None or last is None:
        raise RuntimeError("expected an ordinary import header")
    return {"imports": imports, "first": first, "last": last}


def source(module: str, side: str) -> bytes:
    path = module.replace(".", "/") + ".lean"
    if side == "base":
        return subprocess.check_output(["git", "--no-optional-locks", "show", BASE + ":" + path])
    return Path(path).read_bytes()


def closure(module: str, side: str, graph: dict, hashes: dict) -> set[str]:
    if module not in graph:
        raw = source(module, side)
        hashes[module] = digest(raw)
        graph[module] = [m for m in header(raw)["imports"] if m.startswith("TCSlib.")]
    result = set(graph[module])
    for dep in graph[module]:
        result.update(closure(dep, side, graph, hashes))
    if module in result:
        raise RuntimeError("cyclic import graph")
    return result


def lean_literal(value: str) -> str:
    return json.dumps(value, ensure_ascii=False)


def area_for(side: str, attempt: str | None) -> Path:
    if attempt is not None and not re.fullmatch(r"[a-z][a-z0-9_-]*", attempt):
        raise ValueError("attempt must be a short lowercase identifier such as r2")
    return Path("evidence/rule10") / (side if attempt is None else side + "-" + attempt)


def module_syntax(home: str) -> str:
    """Escape filesystem-derived module components such as `base-r2`."""
    pieces = home.split(".")
    assert all(p and "«" not in p and "»" not in p for p in pieces)
    return ".".join(p if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", p) else "«" + p + "»" for p in pieces)


CENSUS_BODY = r'''
set_option maxHeartbeats 0
open Lean Meta Elab Command

run_cmd do
  let owners : List String := OWNERS
  let env ← getEnv
  let mut seen : Nat := 0
  let mut owned : Nat := 0
  for (n, ci) in env.constants.map₁.toList do
    let some mi := env.getModuleIdxFor? n | continue
    let home := env.header.moduleNames[mi.toNat]!
    unless (`TCSlib).isPrefixOf home || owners.contains home.toString do continue
    let kind := match ci with
      | .axiomInfo _ => "axiom"
      | .defnInfo _ => "def"
      | .thmInfo _ => "theorem"
      | .opaqueInfo _ => "opaque"
      | .quotInfo _ => "quotient"
      | .inductInfo _ => "inductive"
      | .ctorInfo _ => "constructor"
      | .recInfo _ => "recursor"
    let isAbbreviation := match ci with
      | .defnInfo d => match d.hints with
        | .abbrev => true
        | _ => false
      | _ => false
    let mut status : String := "not_definition"
    if ci.isDefinition then
      let s ← liftCoreM <| getReducibilityStatus n
      status := reprStr s
    let matcher := (Match.Extension.getMatcherInfo? env n).isSome
    let row := Json.mkObj [
      ("record", toJson ("constant" : String)),
      ("name", toJson n.toString), ("home", toJson home.toString),
      ("kind", toJson kind), ("abbrev", toJson isAbbreviation),
      ("status", toJson status), ("matcher", toJson matcher)]
    logInfo m!"FILL_CENSUS {row.compress}"
    seen := seen + 1
    if owners.contains home.toString then
      let axs ← liftCoreM <| collectAxioms n
      let names := (axs.qsort (fun a b => a.toString < b.toString)).toList.map (·.toString)
      let row := Json.mkObj [
        ("record", toJson ("axioms" : String)),
        ("name", toJson n.toString), ("home", toJson home.toString),
        ("axioms", toJson names)]
      logInfo m!"FILL_CENSUS {row.compress}"
      owned := owned + 1
  let summary := Json.mkObj [
    ("record", toJson ("complete" : String)),
    ("constants", toJson seen), ("owned", toJson owned),
    ("owners", toJson owners)]
  logInfo m!"FILL_CENSUS {summary.compress}"
'''


def init(side: str, attempt: str | None) -> None:
    area = area_for(side, attempt)
    modules = OWNED[:1] if side == "base" else OWNED
    graph, hashes, entries = {}, {}, []
    for module in modules:
        raw = source(module, side)
        deps = sorted(closure(module, side, graph, hashes))
        write_new(area / "sources" / (module.replace(".", "/") + ".lean"), raw)
        home = module
        if side == "base":
            snapshot = area / "probes/BaseExtraction.lean"
            write_new(snapshot, raw)
            home = snapshot.with_suffix("").as_posix().replace("/", ".")
        entries.append({"module": module, "loaded_home": module_syntax(home), "source_sha256": digest(raw),
                        "import_closure": deps, "header": header(raw)})
    owners = [e["loaded_home"] for e in entries]
    text = "import Lean\n" + "".join("import " + home + "\n" for home in owners)
    text += CENSUS_BODY.replace("OWNERS", "[" + ", ".join(map(lean_literal, owners)) + "]")
    probe = area / "probes/Census.lean"
    write_new(probe, text.encode())
    save_json(area / "init.json", {"base": BASE, "side": side, "attempt": attempt, "entries": entries,
                                  "source_hashes": hashes, "graph": graph,
                                  "census_module": probe.with_suffix("").as_posix(),
                                  "census_source_sha256": digest(text.encode()),
                                  "preparation_tool_sha256": digest(Path(__file__).read_bytes()),
                                  "status": "PREPARED_NOT_RUN"})
    print(f"Prepared {side} census: {probe.with_suffix('').as_posix()}")
    if side == "base":
        print("First check " + (area / "probes/BaseExtraction").as_posix())


def read_census(log: Path, owners: list[str]) -> tuple[dict, dict]:
    constants, axioms, complete = {}, {}, None
    for line in log.read_text().splitlines():
        if TAG not in line:
            continue
        if complete is not None:
            raise RuntimeError("census rows after completion")
        row = json.loads(line.split(TAG, 1)[1])
        if row["record"] == "constant":
            if row["name"] in constants:
                raise RuntimeError("duplicate/ambiguous actual constant name")
            constants[row["name"]] = row
        elif row["record"] == "axioms":
            if row["name"] in axioms:
                raise RuntimeError("duplicate axiom row")
            axioms[row["name"]] = row
        elif row["record"] == "complete":
            complete = row
        else:
            raise RuntimeError("unexpected census record")
    assert complete and complete["constants"] == len(constants)
    assert complete["owners"] == owners and complete["owned"] == len(axioms)
    expected = {n for n, r in constants.items() if r["home"] in owners}
    assert set(axioms) == expected
    assert all(any(r["home"] == owner for r in axioms.values()) for owner in owners)
    return constants, axioms


def seal_command(label: str, requests: list[dict], eof: bool) -> str:
    rows = []
    for row in requests:
        name, home = row["name"], row["home"]
        assert name and home and not any(ord(c) < 32 for c in name + home)
        rows.append(name + "\t" + home)
    payload = "\n".join(rows)
    code = ["set_option maxHeartbeats 0", "run_cmd do",
            "  let label : String := " + lean_literal(label),
            "  let phase : String := " + lean_literal("eof" if eof else "install"),
            "  let payload : String := " + lean_literal(payload),
            f"  let expected : Nat := {len(rows)}",
            "  let env ← Lean.getEnv",
            "  let mut catalog : Std.HashMap String (Array Lean.Name) := {}",
            "  for (n, _) in env.constants.map₁.toList do",
            "    let group := (catalog[n.toString]?).getD #[]",
            "    catalog := catalog.insert n.toString (group.push n)",
            "  let lines := if payload.isEmpty then [] else payload.splitOn \"\\n\"",
            "  let mut verified : Nat := 0",
            "  for line in lines do",
            "    let [spelling, expectedHome] := line.splitOn \"\\t\" |",
            '      throwError "FILL-HARNESS {label}: malformed request"',
            "    let names := (catalog[spelling]?).getD #[]",
            '    unless names.size == 1 do throwError "FILL-HARNESS {label}: absent/ambiguous name {spelling}"',
            "    let n := names[0]!",
            '    let some mi := env.getModuleIdxFor? n | throwError "FILL-HARNESS {label}: missing home {spelling}"',
            "    let home := env.header.moduleNames[mi.toNat]!",
            '    unless home.toString == expectedHome do throwError "FILL-HARNESS {label}: home mismatch {spelling}"',
            '    let some ci := env.find? n | throwError "FILL-HARNESS {label}: missing constant {spelling}"',
            '    unless ci.isDefinition do throwError "FILL-HARNESS {label}: nondefinition {spelling}"']
    if not eof:
        code += ["    let before ← Lean.Elab.Command.liftCoreM <| Lean.getReducibilityStatus n",
                 "    unless before == .irreducible do",
                 "      let id := Lean.mkIdent n",
                 "      Lean.Elab.Command.elabCommand (← `(command| attribute [local irreducible] $id:ident))"]
    code += ["    let installed ← Lean.Elab.Command.liftCoreM <| Lean.getReducibilityStatus n",
             '    unless installed == .irreducible do throwError "FILL-HARNESS {label}: seal inactive at {phase} for {spelling}"',
             "    let row := Lean.Json.mkObj [",
             "      (\"label\", Lean.toJson label), (\"phase\", Lean.toJson phase),",
             "      (\"name\", Lean.toJson n.toString), (\"home\", Lean.toJson home.toString)]",
             '    Lean.logInfo m!"FILL_SEAL_NAME {row.compress}"',
             "    verified := verified + 1",
             '  unless verified == expected do throwError "FILL-HARNESS {label}: count mismatch {verified} vs {expected}"',
             '  Lean.logInfo m!"FILL_SEAL_DONE {label} {phase} {expected} {verified}"', ""]
    return "\n".join(code)


def instrument(raw: bytes, label: str, requests: list[dict]) -> tuple[bytes, list[dict], list[dict]]:
    text = raw.decode()
    info = header(raw)
    additions = []
    if "Lean" not in info["imports"]:
        additions.append((info["first"], "import_Lean", "import Lean\n"))
    additions += [(info["last"], "install", "\n" + seal_command(label, requests, False) + "\n"),
                  (len(text), "eof", "\n" + seal_command(label, requests, True))]
    additions.sort(key=lambda entry: entry[0])
    result, cursor, edits = "", 0, []
    for offset, kind, added in additions:
        result += text[cursor:offset]
        edits.append({"kind": kind, "source_character_offset": offset,
                      "probe_character_offset": len(result), "characters": len(added),
                      "probe_byte_offset": len(result.encode()), "bytes": len(added.encode()),
                      "sha256": digest(added.encode())})
        result += added
        cursor = offset
    result += text[cursor:]
    recovered = result.encode()
    for edit in reversed(edits):
        offset = edit["probe_byte_offset"]
        recovered = recovered[:offset] + recovered[offset + edit["bytes"]:]
    assert recovered == raw
    starts = [0] + [match.end() for match in re.finditer("\n", text) if match.end() < len(text)]
    lines = [{"source_line": i + 1,
              "probe_line": i + 1 + sum(s.count("\n") for at, _, s in additions if at <= offset)}
             for i, offset in enumerate(starts)]
    return result.encode(), edits, lines


CONTROL_SOURCE = {
    "PadFin": (
        "import TCSlib.Cryptography.Asymptotic.Adversary\n"
        "open TCSlib.Cryptography\n"
        "example (w : List Bool) : padFin 1 w 0 = w.getD 0 false := by rfl\n",
        "TCSlib.Cryptography.padFin"),
    "RunAtL": (
        "import TCSlib.Complexity.Randomized.PPT\n"
        "open Complexity Turing\n"
        "example (A : NUPPT) (n : Nat) (y r : List Bool) :\n"
        "    A.runAtL n y r = A.output (pairEncode (pairEncode (NUPPT.advInput n y) (A.advice n)) r) := by rfl\n",
        "Complexity.NUPPT.runAtL"),
    "PolyEval": (
        "import TCSlib.Complexity.Randomized.PolyExpr\n"
        "open Complexity\n"
        "example (n : Nat) : PolyExpr.eval .var n = n := by rfl\n",
        EVAL),
}


def prepare_seals(side: str, census_log: Path, attempt: str | None) -> None:
    area = area_for(side, attempt)
    config = json.loads((area / "init.json").read_bytes())
    assert config["base"] == BASE and config["side"] == side and config.get("attempt") == attempt
    result = json.loads(census_log.with_suffix(".json").read_bytes())
    assert result["rc"] == 0 and result["fresh_nonempty_object"] and not result["errors"]
    assert result["source_unchanged"] and result["source_sha256"] == config["census_source_sha256"]
    assert result["log_sha256"] == digest(census_log.read_bytes())
    constants, axioms = read_census(census_log, [e["loaded_home"] for e in config["entries"]])
    probes, exclusions = [], []
    for entry in config["entries"]:
        module = entry["module"]
        raw = (area / "sources" / (module.replace(".", "/") + ".lean")).read_bytes()
        assert digest(raw) == entry["source_sha256"]
        candidates = [r for r in constants.values() if r["home"] in entry["import_closure"] and r["kind"] == "def"]
        # Actual abbreviation hints are excluded, not every reducible definition.
        # Generated matchers stay in the candidate set even if marked reducible.
        abbrevs = [r for r in candidates if r["abbrev"] and not r["matcher"]]
        assert all(r["status"].rsplit(".", 1)[-1] == "reducible" for r in abbrevs)
        candidates = [r for r in candidates if r not in abbrevs]
        exclusions.append({"module": module, "validated_abbreviations": abbrevs})
        for variant in ("A", "B"):
            requested = sorted((r for r in candidates if variant == "B" or r["name"] != EVAL), key=lambda r: r["name"])
            label = "Seal" + variant + "_" + module.rsplit(".", 1)[-1]
            probe, edits, lines = instrument(raw, label, requested)
            path = area / "probes" / (label + ".lean")
            write_new(path, probe)
            row = {"label": label, "source": module.replace(".", "/") + ".lean", "variant": variant,
                   "module": path.with_suffix("").as_posix(), "requests": requested,
                   "source_sha256": digest(raw), "probe_sha256": digest(probe),
                   "insertions": edits, "line_map": lines, "expected_errors": 0}
            probes.append(row)
            save_json(area / "requests" / (label + ".json"), row)
    controls = []
    for label, (text, name) in CONTROL_SOURCE.items():
        assert name in constants and constants[name]["kind"] == "def" and not constants[name]["abbrev"]
        raw = text.encode()
        unsealed = area / "probes" / ("Control" + label + "Unsealed.lean")
        write_new(unsealed, raw)
        controls.append({"label": "Control" + label + "Unsealed", "module": unsealed.with_suffix("").as_posix(),
                         "expected_errors": 0, "probe_sha256": digest(raw), "requests": []})
        for variant in ("A", "B"):
            seal_label = "Control" + label + variant
            requests = [] if label == "PolyEval" and variant == "A" else [constants[name]]
            probe, edits, lines = instrument(raw, seal_label, requests)
            path = area / "probes" / (seal_label + ".lean")
            write_new(path, probe)
            controls.append({"label": seal_label, "module": path.with_suffix("").as_posix(),
                             "expected_errors": int(bool(requests)), "requests": requests,
                             "probe_sha256": digest(probe), "source_sha256": digest(raw),
                             "insertions": edits, "line_map": lines})
    # Reader controls should remain valid with the same foreign definitions sealed.
    reader_text = (
        "import TCSlib.Cryptography.Asymptotic.Adversary\n"
        "open Complexity Turing TCSlib.Cryptography\n"
        "example (w : List Bool) : padFin 1 w 0 = w.getD 0 false := by exact padFin_apply 1 w 0\n"
        "example (A : NUPPT) (n : Nat) (y r : List Bool) :\n"
        "    A.runAtL n y r = A.output (pairEncode (pairEncode (NUPPT.advInput n y) (A.advice n)) r) :=\n"
        "  by exact NUPPT.runAtL_eq A n y r\n"
        "example (n : Nat) : PolyExpr.eval .var n = n := by exact PolyExpr.eval_var n\n").encode()
    for variant in ("A", "B"):
        names = ["TCSlib.Cryptography.padFin", "Complexity.NUPPT.runAtL"] + ([EVAL] if variant == "B" else [])
        requests = [constants[n] for n in names]
        label = "ControlReaders" + variant
        probe, edits, lines = instrument(reader_text, label, requests)
        path = area / "probes" / (label + ".lean")
        write_new(path, probe)
        controls.append({"label": label, "module": path.with_suffix("").as_posix(),
                         "expected_errors": 0, "requests": requests, "probe_sha256": digest(probe),
                         "source_sha256": digest(reader_text), "insertions": edits, "line_map": lines})
    save_json(area / "all-stored-axioms.json", list(axioms.values()))
    save_json(area / "census-constants.json", list(constants.values()))
    save_json(area / "abbreviation-exclusions.json", exclusions)
    save_json(area / "manifest.json", {"base": BASE, "side": side, "attempt": attempt,
                                      "census_log": str(census_log), "census_log_sha256": digest(census_log.read_bytes()),
                                      "init_sha256": digest((area / "init.json").read_bytes()),
                                      "status": "PREPARED_NOT_RUN", "seals": probes, "controls": controls})
    print(f"Prepared {len(probes)} whole-file seals and {len(controls)} controls for {side}")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=("init", "seals"))
    parser.add_argument("side", choices=("base", "final"))
    parser.add_argument("--census-log", type=Path)
    parser.add_argument("--attempt", help="fresh evidence suffix, e.g. r2; preserves prior areas")
    args = parser.parse_args()
    if args.action == "init":
        init(args.side, args.attempt)
    else:
        assert args.census_log, "seals requires the completed raw census log"
        prepare_seals(args.side, args.census_log, args.attempt)


if __name__ == "__main__":
    main()
