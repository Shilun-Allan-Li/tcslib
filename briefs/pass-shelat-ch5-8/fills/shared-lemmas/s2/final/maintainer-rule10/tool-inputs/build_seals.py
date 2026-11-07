"""Prepare, but never run, the 51 Gate06 whole-file conservative seals.

Usage (from the integration worktree):
  python3 -I .lake/ps-maintainer/gate06/build_seals.py EVIDENCE_DIRECTORY

EVIDENCE_DIRECTORY is the completed evidence-rule10-r2 directory, which may
live in the records checkout. Read-only Git commands verify the pinned library.
Only ignored scratch probes and evidence .source.txt/JSON files are written.
The root coordinator reviews this script and runs/checks probes separately.
"""

from __future__ import annotations

import argparse
import datetime
import hashlib
import io
import json
from pathlib import Path
import re
import subprocess
import sys
import tarfile


EXPECTED_MODULES = 51
REQUEST_CHUNK_SIZE = 128
SCRATCH_REL = Path(".lake/ps-maintainer/gate06/rule10")
NOTATION_EXCLUSIONS = frozenset({
    "Complexity.PolyExpr.eval",
    "TCSlib.Cryptography.glNeed",
})
MODULE_RE = re.compile(r"TCSlib(?:\.[A-Za-z_][A-Za-z0-9_']*)+")
IMPORT_RE = re.compile(r"import\s+([A-Za-z_][A-Za-z0-9_'.]*(?:[ \t]+[A-Za-z_][A-Za-z0-9_'.]*)*)")
DECL_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec)\s+)*"
    r"(?:theorem|lemma|def|instance|structure|inductive|abbrev|class|opaque|axiom)\b",
    re.M,
)
SHA_RE = re.compile(r"[0-9a-f]{64}")
COMMIT_RE = re.compile(r"[0-9a-f]{40}")


class PreparationError(RuntimeError):
    """Fail closed without calling Lean or overwriting a previous preparation."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise PreparationError(message)


def sha(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def unique_object(pairs: list[tuple[str, object]]) -> dict:
    result = {}
    for key, value in pairs:
        require(key not in result, f"duplicate JSON key: {key}")
        result[key] = value
    return result


def read_json(path: Path, captured: dict[str, bytes]) -> dict:
    raw = path.read_bytes()
    captured[path.name] = raw
    value = json.loads(raw, object_pairs_hook=unique_object)
    require(isinstance(value, dict), f"{path.name}: expected JSON object")
    return value


def git(root: Path, *args: str) -> bytes:
    # --no-optional-locks also prevents read-only status/index refresh writes.
    return subprocess.check_output(
        ["git", "--no-optional-locks", "-C", str(root), *args],
        stderr=subprocess.PIPE,
    )


def library_snapshot(root: Path, pins: dict) -> tuple[dict[str, bytes], dict]:
    for field in ("base", "head"):
        require(isinstance(pins.get(field), str) and COMMIT_RE.fullmatch(pins[field]) is not None,
                f"pins.{field}: expected full commit SHA")
    require(pins.get("base_is_ancestor") is True, "pins do not assert base ancestry")
    require(pins.get("library_sources_equal_head") is True, "pins do not assert pinned library bytes")
    require(pins.get("untracked_or_ignored_library_lean_files") == 0,
            "pins report extra library Lean files")
    head = git(root, "rev-parse", "HEAD").decode().strip()
    require(head == pins["head"], f"HEAD differs from pins: {head}")
    git(root, "merge-base", "--is-ancestor", pins["base"], head)
    tree = git(root, "rev-parse", head + ":TCSlib").decode().strip()
    require(tree == pins.get("library_git_tree"), "TCSlib tree differs from pins")
    archive = git(root, "archive", "--format=tar", head, "--", "TCSlib", "TCSlib.lean")
    with tarfile.open(fileobj=io.BytesIO(archive)) as saved:
        committed = {}
        for item in saved.getmembers():
            if item.name.endswith(".lean"):
                require(item.isfile(), f"non-ordinary pinned library source: {item.name}")
                handle = saved.extractfile(item)
                require(handle is not None, f"missing archived bytes: {item.name}")
                committed[item.name] = handle.read()
    paths = {p.relative_to(root).as_posix() for p in (root / "TCSlib").rglob("*.lean")}
    paths.add("TCSlib.lean")
    require(paths == set(committed),
            f"extra/missing library source: extra={sorted(paths - set(committed))}, "
            f"missing={sorted(set(committed) - paths)}")
    for path, raw in committed.items():
        source = root / path
        require(source.is_file() and not source.is_symlink(), f"non-ordinary current source: {path}")
        require(source.read_bytes() == raw, f"library bytes differ from pinned HEAD: {path}")
    digest = sha("".join(f"{p}\t{sha(committed[p])}\n" for p in sorted(committed)).encode())
    return committed, {"head": head, "base": pins["base"], "library_git_tree": tree,
                       "library_file_count": len(committed), "library_content_sha256": digest,
                       "source_bytes_equal_head": True, "base_is_ancestor": True}


def blank_comments_strings(text: str) -> str:
    """Keep character/newline positions, blank nested comments and string literals.

    This is an independent, preparation-only header lexer, not an execution of
    a repository parser. Unsupported import layouts are rejected by header().
    """
    chars = list(text)
    i, depth = 0, 0

    def blank(a: int, b: int) -> None:
        for k in range(a, b):
            if chars[k] not in "\r\n":
                chars[k] = " "

    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                blank(i, i + 2)
                i, depth = i + 2, depth + 1
            elif text.startswith("-/", i):
                blank(i, i + 2)
                i, depth = i + 2, depth - 1
            else:
                blank(i, i + 1)
                i += 1
        elif text.startswith("/-", i):
            blank(i, i + 2)
            i, depth = i + 2, 1
        elif text.startswith("--", i):
            end = text.find("\n", i)
            end = len(text) if end == -1 else end
            blank(i, end)
            i = end
        else:
            # Lean raw strings r"...", r#"..."#, etc.; normal identifiers
            # ending in r followed by a quote are not header import syntax.
            raw = re.match(r'r(#+)?"', text[i:]) if text[i] == "r" else None
            if raw:
                fence = '"' + (raw.group(1) or "")
                end = text.find(fence, i + len(raw.group(0)))
                require(end != -1, "unclosed raw string in source")
                end += len(fence)
                blank(i, end)
                i = end
            elif text[i] == '"':
                end = i + 1
                while end < len(text) and text[end] != '"':
                    end += 2 if text[end] == "\\" else 1
                require(end < len(text), "unclosed string in source")
                blank(i, end + 1)
                i = end + 1
            elif text[i] == "'":
                char = re.match(r"'(?:[^'\\\r\n]|\\(?:x[0-9a-fA-F]{2}|u[0-9a-fA-F]{4}|.))'", text[i:])
                if char:
                    blank(i, i + len(char.group(0)))
                    i += len(char.group(0))
                else:
                    i += 1
            else:
                i += 1
    require(depth == 0, "unclosed block comment in source")
    return "".join(chars)


def header(raw: bytes) -> dict:
    text = raw.decode("utf-8")
    code = blank_comments_strings(text)
    raw_lines, code_lines = raw.split(b"\n"), code.split("\n")
    require(len(raw_lines) == len(code_lines), "header lexer changed line count")
    imports, first_import, last_import, first_active = [], None, None, None
    closed, offset = False, 0
    for index, (raw_line, line) in enumerate(zip(raw_lines, code_lines)):
        end = offset + len(raw_line) + (index < len(raw_lines) - 1)
        active = line.strip()
        if active:
            if first_active is None:
                first_active = offset
            match = IMPORT_RE.fullmatch(active)
            if match:
                require(not closed, "import occurs after a source command; unsupported header")
                if first_import is None:
                    first_import = offset
                last_import = end
                imports.extend(match.group(1).split())
            else:
                require(not re.match(r"(?:prelude|(?:public\s+|meta\s+)?import)\b", active),
                        f"unsupported import/prelude layout: {active[:100]}")
                closed = True
        offset = end
    return {"imports": imports, "first_import_offset": first_import,
            "last_import_end_offset": last_import,
            "first_active_offset": len(raw) if first_active is None else first_active,
            "code": code}


def validate_metadata(root: Path, pins: dict, modules: dict, closures: dict,
                      fingerprints: dict, touched: dict, library: dict[str, bytes]) -> tuple[dict, dict]:
    require(len(modules) == EXPECTED_MODULES == pins.get("audited_math_modules"),
            "expected exactly 51 math modules in modules.json and pins.json")
    require(set(closures) == set(modules) == set(touched), "module/closure/touched keys differ")
    changed = git(root, "diff", "--name-only", pins["base"], pins["head"], "--", "*.lean").decode().splitlines()
    require(set(changed) == set(fingerprints) and len(changed) == pins.get("changed_lean_files"),
            "changed Lean paths do not match fingerprints/pins")
    for path, digest in fingerprints.items():
        require(path in library and isinstance(digest, str) and SHA_RE.fullmatch(digest) is not None,
                f"invalid/nonlibrary source fingerprint: {path}")
        require(sha(library[path]) == digest, f"source fingerprint differs: {path}")
    headers, normalized = {}, {}
    for module, path in modules.items():
        require(isinstance(module, str) and MODULE_RE.fullmatch(module) is not None,
                f"unsupported module name: {module!r}")
        require(path == module.replace(".", "/") + ".lean" and path in fingerprints,
                f"module/source mapping mismatch: {module}")
        headers[module] = header(library[path])
        require(DECL_RE.search(headers[module]["code"]) is not None,
                f"math target contains no stored-declaration command: {module}")
        deps = closures[module]
        require(isinstance(deps, list) and all(isinstance(d, str) and MODULE_RE.fullmatch(d) for d in deps),
                f"invalid closure list: {module}")
        require(deps == sorted(set(deps)) and module not in deps, f"duplicate/self/unsorted closure: {module}")
        names = touched[module]
        require(isinstance(names, list) and all(isinstance(n, str) and n for n in names),
                f"invalid touched source names: {module}")
        normalized[module] = [{"source_spelling": n, "normalized_spelling": n.removeprefix("_root_."),
                               "removed_root_prefix": n.startswith("_root_.")} for n in names]

    def imports(module: str) -> list[str]:
        if module not in headers:
            path = module.replace(".", "/") + ".lean"
            require(path in library, f"missing imported TCSlib source: {module}")
            headers[module] = header(library[path])
        return [m for m in headers[module]["imports"] if m == "TCSlib" or m.startswith("TCSlib.")]

    for module in modules:
        found, stack = set(), imports(module).copy()
        while stack:
            dep = stack.pop()
            if dep not in found:
                found.add(dep)
                stack.extend(imports(dep))
        require(sorted(found) == closures[module], f"current import closure differs from metadata: {module}")
    excluded = pins.get("excluded_import_option_only_files")
    require(isinstance(excluded, list) and set(excluded) == set(changed) - set(modules.values()),
            "excluded paths do not exactly complement math targets")
    for path in excluded:
        active = [s.strip() for s in blank_comments_strings(library[path].decode()).splitlines() if s.strip()]
        require(all(IMPORT_RE.fullmatch(s) or re.fullmatch(r"set_option\s+\S+\s+\S+", s) for s in active),
                f"excluded source has commands beyond imports/options: {path}")
    return headers, normalized


def completed_collector(root: Path, evidence: Path, captured: dict[str, bytes],
                        modules: dict, closures: dict) -> tuple[str, dict, list[str]]:
    result = read_json(evidence / "collect1.json", captured)
    require(result.get("rc") == 0 and result.get("end"), "collect1 is not completed with rc 0")
    require(result.get("source_unchanged") is True and result.get("fresh_nonempty_object") is True,
            "collect1 source/object completion checks failed")
    require(result.get("error_diagnostics") == 0, "collect1 reports Lean errors")
    require(result.get("label") == "collect1", "wrong collector result label")
    collector = root / SCRATCH_REL / "Collect.lean"
    given_module = result.get("module")
    require(isinstance(given_module, str) and (root / (given_module + ".lean")).resolve() == collector.resolve(),
            "collector result names the wrong probe")
    for name in ("collect1.log", "collect1.source.txt", "Collect.source.txt"):
        captured[name] = (evidence / name).read_bytes()
    raw = captured["collect1.source.txt"]
    require(raw == captured["Collect.source.txt"] == collector.read_bytes(), "collector source copies differ")
    require(sha(raw) == result.get("source_sha256"), "collector source SHA differs from result")
    log = captured["collect1.log"].decode("utf-8")
    footers = re.findall(r"(?m)^END (\S+) RC (-?\d+)\s*$", log)
    require(footers == [(result["end"], "0")] and log.rstrip().endswith("RC 0"),
            "collector log lacks one matching final successful END marker")
    require(re.findall(r"(?m)^START (\S+)\s*$", log) == [result.get("start")], "collector START marker differs")
    require(re.findall(r"(?m)^SOURCE_SHA256 ([0-9a-f]{64})\s*$", log) == [sha(raw)],
            "collector log source SHA differs")
    require(not re.search(r"\.lean:\d+:\d+: error:", log), "collector log has error diagnostics")
    require("TOUCHED-NOT-FOUND" not in log and "AXIOMS-NOT-FOUND" not in log,
            "collector has unmatched coverage warnings")
    lines = raw.decode("utf-8").splitlines()
    for command in ("#collect", "#axs", "#sealclosure"):
        got = [s for s in lines if s.startswith(command + " ")]
        expected = [(command + " " + m + (' ["*"]' if command != "#sealclosure" else
                     " [" + ", ".join(closures[m]) + "]")) for m in modules]
        require(got == expected, f"collector is not the exact all-module/all-stored {command} command set")
    require([s for s in lines if s.startswith("import ")] == ["import Lean", *("import " + m for m in modules)],
            "collector import set/order differs from modules.json")
    warnings = [s for s in log.splitlines() if "warning:" in s]
    return log, result, warnings


def collector_rows(log: str, modules: dict, closures: dict) -> tuple[dict, dict, dict]:
    terms = {m: {} for m in modules}
    closure_rows = {m: {} for m in modules}
    summaries, axioms = {}, {m: [] for m in modules}
    for line_no, line in enumerate(log.splitlines(), 1):
        match = re.search(r"\b(SEALROW|CLOSUREROW) (.+)$", line)
        if match:
            kind, rest = match.groups()
            fields = rest.split(" | ")
            require(len(fields) == 5, f"malformed {kind} at log line {line_no}")
            module, name, home, matcher, status = (s.strip() for s in fields)
            require(module in modules and home in closures[module], f"{kind} outside module import closure: {rest}")
            require(name and not any(ord(c) < 32 for c in name), f"invalid printed name: {name!r}")
            require(matcher in {"matcher=true", "matcher=false"}, f"bad matcher field: {rest}")
            status_name = status.rsplit(".", 1)[-1]
            require(status_name in {"reducible", "semireducible", "irreducible"}, f"bad status: {rest}")
            require(status_name != "reducible" or matcher == "matcher=true", f"ordinary reducible row: {rest}")
            target = terms if kind == "SEALROW" else closure_rows
            require(name not in target[module], f"duplicate/ambiguous printed {kind} name: {module} | {name}")
            target[module][name] = {"spelling": name, "home": home, "matcher": matcher == "matcher=true",
                                    "collector_reducibility": status_name, "collector_log_line": line_no}
        summary = re.search(r"\bMODULE (\S+): touched (\d+), constants (\d+), reached (\d+)\s*$", line)
        if summary:
            module, count, constants, reached = summary.groups()
            require(module in modules and module not in summaries and count == "1", "bad/duplicate MODULE summary")
            summaries[module] = {"wildcard_count": int(count), "stored_constants": int(constants), "reached": int(reached)}
        ax = re.search(r"\bAXIOMSID (.+)$", line)
        if ax:
            fields = ax.group(1).split(" | ", 3)
            require(len(fields) == 4 and fields[0] in modules and fields[2].startswith("display="),
                    f"malformed AXIOMSID at log line {line_no}")
            axioms[fields[0]].append({"printed_actual_name": fields[1], "display": fields[2][8:],
                                      "axioms_display": fields[3], "collector_log_line": line_no})
    require(set(summaries) == set(modules), "missing MODULE summaries: collector incomplete")
    inventory = {}
    for module in modules:
        require(len(axioms[module]) == summaries[module]["stored_constants"],
                f"AXIOMSID row count differs from all-stored MODULE count: {module}")
        filtered_terms = {n: r for n, r in terms[module].items() if n not in NOTATION_EXCLUSIONS}
        filtered_closure = {n: r for n, r in closure_rows[module].items() if n not in NOTATION_EXCLUSIONS}
        missing = sorted(set(filtered_terms) - set(filtered_closure))
        require(not missing, f"term SEALROW names missing from conservative closure for {module}: {missing}")
        for name, row in filtered_terms.items():
            other = filtered_closure[name]
            require(all(row[f] == other[f] for f in ("home", "matcher", "collector_reducibility")),
                    f"term/closure row identity metadata differs: {module} | {name}")
        inventory[module] = {**summaries[module], "axioms": axioms[module],
                             "term_names_before_notation_exclusions": sorted(terms[module]),
                             "term_notation_exclusions": sorted(set(terms[module]) & NOTATION_EXCLUSIONS),
                             "closure_notation_exclusions": sorted(set(closure_rows[module]) & NOTATION_EXCLUSIONS),
                             "term_names": sorted(filtered_terms), "closure_names": sorted(filtered_closure),
                             "term_subset_of_closure": True}
        terms[module], closure_rows[module] = filtered_terms, filtered_closure
    return terms, closure_rows, inventory


def lean_string(value: str) -> str:
    require(not any(ord(c) < 32 for c in value), "control character in generated Lean string")
    return json.dumps(value, ensure_ascii=False)


def seal_command(label: str, rows: list[dict], *, end: bool) -> bytes:
    pairs = ["    (" + lean_string(r["spelling"]) + ", " + lean_string(r["home"]) + ")" for r in rows]
    # Installation precedes the original source options. Give the harness its
    # own heartbeat budget, and avoid one deeply nested, huge array literal.
    # Neither setting creates a command scope around the local attributes.
    lines = [f"/- G06-HARNESS {'EOF-VERIFY' if end else 'INSTALL'} {label} -/",
             "set_option maxHeartbeats 0", "run_cmd do",
             "  let label : String := " + lean_string(label),
             "  let mut requests : Array (String × String) := #[]"]
    for start in range(0, len(pairs), REQUEST_CHUNK_SIZE):
        lines += ["  requests := requests ++ #[", ",\n".join(pairs[start:start + REQUEST_CHUNK_SIZE]), "  ]"]
    lines += ["  let env ← Lean.getEnv",
             "  let mut catalog : Std.HashMap String (Array Lean.Name) := {}",
             "  let mut verified : Nat := 0"]
    if not end:
        lines += ["  let mut active : Nat := 0", "  let mut already : Nat := 0"]
    lines += [
        "  for (n, _) in env.constants.map₁.toList do",
        "    let some mi := env.getModuleIdxFor? n | continue",
        "    unless (`TCSlib).isPrefixOf env.header.moduleNames[mi.toNat]! do continue",
        "    let ns := (catalog[n.toString]?).getD #[]",
        "    catalog := catalog.insert n.toString (ns.push n)",
        "  for (spelling, expectedHome) in requests do",
        "    let ns := (catalog[spelling]?).getD #[]",
        '    unless ns.size == 1 do throwError "G06-HARNESS {label}: absent/ambiguous imported name {spelling}; candidates={ns.size}"',
        "    let n := ns[0]!",
        '    let some mi := env.getModuleIdxFor? n | throwError "G06-HARNESS {label}: no home for {spelling}"',
        "    let home := env.header.moduleNames[mi.toNat]!",
        '    unless home.toString == expectedHome do throwError "G06-HARNESS {label}: home differs for {spelling}: {home}"',
        '    let some ci := env.find? n | throwError "G06-HARNESS {label}: no constant for {spelling}"',
        '    unless ci.isDefinition do throwError "G06-HARNESS {label}: requested nondefinition {spelling}"',
    ]
    if not end:
        lines += [
            "    let before ← Lean.Elab.Command.liftCoreM <| Lean.getReducibilityStatus n",
            "    if before == .irreducible then",
            "      already := already + 1",
            "    else",
            "      let id := Lean.mkIdent n",
            "      Lean.Elab.Command.elabCommand (← `(command| attribute [local irreducible] $id:ident))",
            "      active := active + 1",
        ]
    lines += [
        "    let installed ← Lean.Elab.Command.liftCoreM <| Lean.getReducibilityStatus n",
        '    unless installed == .irreducible do throwError "G06-HARNESS {label}: seal not installed' +
        (' at EOF' if end else '') + ' for {spelling}"',
        "    verified := verified + 1",
    ]
    if not end:
        lines += [
            '    Lean.logInfo m!"G06-NAME label={label} spelling={spelling} actual={n.toString} home={home} before={repr before} installed={repr installed}"',
            '  unless active + already == requests.size do throwError "G06-HARNESS {label}: installation count mismatch"',
        ]
    lines += ['  unless verified == requests.size do throwError "G06-HARNESS {label}: verification count mismatch"']
    if end:
        lines += ['  Lean.logInfo m!"G06-SEAL-END label={label} requested={requests.size} verified={verified}"']
    else:
        lines += ['  Lean.logInfo m!"G06-SEAL label={label} requested={requests.size} active={active} already_irreducible={already} verified={verified}"']
    return ("\n".join(lines) + "\n\n").encode("utf-8")


def instrument(raw: bytes, info: dict, label: str, rows: list[dict]) -> tuple[bytes, list[dict], list[dict]]:
    # Edits are insertions in original-byte coordinates. Stable ordering handles
    # no-import or empty-source cases without changing any original byte.
    first = info["first_import_offset"]
    import_at = info["first_active_offset"] if first is None else first
    seal_at = info["first_active_offset"] if first is None else info["last_import_end_offset"]
    inserts = []
    if "Lean" not in info["imports"]:
        prefix = b"\n" if import_at and raw[import_at - 1:import_at] != b"\n" else b""
        inserts.append((import_at, "import_Lean", prefix + b"import Lean\n"))
    prefix = b"\n" if seal_at and raw[seal_at - 1:seal_at] != b"\n" else b""
    inserts.append((seal_at, "seal_preamble", prefix + seal_command(label, rows, end=False)))
    prefix = b"\n" if raw and not raw.endswith(b"\n") else b""
    inserts.append((len(raw), "seal_eof_verifier", prefix + seal_command(label, rows, end=True)))
    inserts.sort(key=lambda item: item[0])
    output, cursor, records = bytearray(), 0, []
    for original_offset, kind, addition in inserts:
        output.extend(raw[cursor:original_offset])
        probe_offset = len(output)
        output.extend(addition)
        records.append({"kind": kind, "original_byte_offset": original_offset,
                        "probe_byte_offset": probe_offset, "byte_count": len(addition),
                        "sha256": sha(addition), "newline_count": addition.count(b"\n"),
                        "probe_start_line": bytes(output[:probe_offset]).count(b"\n") + 1,
                        "probe_end_line": bytes(output).count(b"\n")})
        cursor = original_offset
    output.extend(raw[cursor:])
    probe = bytes(output)
    recovered = probe
    for record in reversed(records):
        offset, length = record["probe_byte_offset"], record["byte_count"]
        recovered = recovered[:offset] + recovered[offset + length:]
    require(recovered == raw, f"original-byte preservation check failed: {label}")
    line_map, offset = [], 0
    # Map each existing original line start to its new line; instrumentation
    # ranges above distinguish harness diagnostics from source diagnostics.
    starts = [0] + [m.end() for m in re.finditer(b"\n", raw) if m.end() < len(raw)]
    for line, offset in enumerate(starts, 1):
        shift = sum(addition.count(b"\n") for at, _, addition in inserts if at <= offset)
        line_map.append({"source_line": line, "probe_line": line + shift})
    return probe, records, line_map


def json_bytes(value: object) -> bytes:
    return (json.dumps(value, indent=2, ensure_ascii=False) + "\n").encode("utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("evidence_directory", type=Path)
    parser.add_argument("--root", type=Path, default=Path.cwd(), help="integration worktree (default: cwd)")
    args = parser.parse_args()
    root, evidence = args.root.resolve(), args.evidence_directory.resolve()
    require(evidence.is_dir(), "completed evidence directory does not exist")
    require(not evidence.is_relative_to(root / "TCSlib"), "evidence must be outside library sources")
    captured = {}
    pins = read_json(evidence / "pins.json", captured)
    modules = read_json(evidence / "modules.json", captured)
    closures = read_json(evidence / "closures.json", captured)
    fingerprints = read_json(evidence / "source-fingerprints.json", captured)
    touched = read_json(evidence / "touched.json", captured)
    # Fail before any write while the collector is still running.
    require((evidence / "collect1.json").is_file(), "collect1 has no completion JSON; no probes prepared")
    library, library_check = library_snapshot(root, pins)
    headers, normalized_touched = validate_metadata(root, pins, modules, closures, fingerprints, touched, library)
    log, collector_result, warnings = completed_collector(root, evidence, captured, modules, closures)
    terms, conservative, inventory = collector_rows(log, modules, closures)
    scratch = root / SCRATCH_REL / "seals"
    saved = evidence / "seals"
    builder = Path(__file__).read_bytes()
    manifest = {"status": "PREPARED_NOT_RUN", "created_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
                "builder_sha256": sha(builder), "root": str(root), "evidence_directory": str(evidence),
                "library_verification": library_check, "collector_result": collector_result,
                "input_sha256": {name: sha(raw) for name, raw in sorted(captured.items())},
                "notation_exclusions_exact": sorted(NOTATION_EXCLUSIONS),
                "warnings": warnings, "collector_warnings_present": bool(warnings),
                "name_resolution": "imported TCSlib-home constants -> String to Array actual Lean.Name catalog; unique actual candidate; mkIdent n",
                "runtime_checks_pending": ["preamble actual-name/home/definition resolution", "local irreducible installation and counts",
                                           "EOF installed-status verification", "whole-file Lean check and diagnostics classification"],
                "limitations": ["No Lean process was launched by this preparation script.",
                                "Prepared probes are not passing audit evidence until run and reviewed.",
                                "Anonymous commands are covered conservatively by the complete import-closure seal.",
                                "Core/Mathlib explicit-unfold policy checks and positive/negative controls remain separate.",
                                "Notation exclusions are exact names only; their matcher descendants are retained."],
                "probes": []}
    planned = []
    for index, module in enumerate(sorted(modules), 1):
        label = f"G06Seal_{index:03d}_" + module.replace(".", "_").replace("'", "_prime")
        rows = [conservative[module][n] for n in sorted(conservative[module])]
        raw = library[modules[module]]
        probe, insertions, line_map = instrument(raw, headers[module], label, rows)
        probe_path, source_path = scratch / (label + ".lean"), saved / (label + ".source.txt")
        record = {"ordinal": index, "label": label, "module": module, "source": modules[module],
                  "source_sha256": sha(raw), "probe_sha256": sha(probe),
                  "probe_path": str(probe_path), "probe_module": probe_path.relative_to(root).with_suffix("").as_posix(),
                  "saved_source": str(source_path), "status": "PREPARED_NOT_RUN",
                  "original_bytes_preserved": True, "insertions": insertions, "source_to_probe_lines": line_map,
                  "preamble_lines": next({"start": r["probe_start_line"], "end": r["probe_end_line"]}
                                         for r in insertions if r["kind"] == "seal_preamble"),
                  "eof_verifier_lines": next({"start": r["probe_start_line"], "end": r["probe_end_line"]}
                                             for r in insertions if r["kind"] == "seal_eof_verifier"),
                  "request_literal_chunk_size": REQUEST_CHUNK_SIZE,
                  "source_imports": headers[module]["imports"], "import_closure": closures[module],
                  "touched_source_names": normalized_touched[module],
                  "term_names": sorted(terms[module]), "requested_names": rows,
                  "requested_count": len(rows), "term_subset_of_closure": True,
                  "collector_irreducible_count": sum(r["collector_reducibility"] == "irreducible" for r in rows),
                  "collector_active_candidate_count": sum(r["collector_reducibility"] != "irreducible" for r in rows),
                  "runtime_identity_and_installed_status_verified": False}
        manifest["probes"].append(record)
        planned += [(probe_path, probe), (source_path, probe), (saved / (label + ".json"), json_bytes(record))]
    require(len(manifest["probes"]) == EXPECTED_MODULES, "not exactly 51 planned probes")
    planned += [(evidence / "seal-manifest.json", json_bytes(manifest)),
                (evidence / "seal-collector-inventory.json", json_bytes(inventory)),
                (evidence / "seal-preparation-warnings.json", json_bytes({"warnings": warnings, "count": len(warnings),
                                                                         "status": "PREPARED_NOT_RUN"})),
                (evidence / "build_seals.py", builder)]
    require(len({path for path, _ in planned}) == len(planned), "duplicate generated path")
    for path, _ in planned:
        require(not path.exists(), f"refusing to overwrite previous preparation: {path}")
    # Recheck all pinned sources and consumed evidence just before publishing.
    # This does not lock the worktree: root must keep sources frozen while running.
    for path, raw in library.items():
        require((root / path).read_bytes() == raw, f"library changed during preparation: {path}")
    require(git(root, "rev-parse", "HEAD").decode().strip() == pins["head"], "HEAD changed during preparation")
    for name, raw in captured.items():
        require((evidence / name).read_bytes() == raw, f"input evidence changed during preparation: {name}")
    for path, content in planned:
        path.parent.mkdir(parents=True, exist_ok=True)
        with path.open("xb") as handle:
            handle.write(content)
    print(json.dumps({"status": "PREPARED_NOT_RUN", "modules": len(manifest["probes"]),
                      "manifest": str(evidence / "seal-manifest.json"), "warnings": len(warnings),
                      "lean_processes_started": 0}))


if __name__ == "__main__":
    try:
        main()
    except (PreparationError, OSError, ValueError, subprocess.CalledProcessError) as error:
        print(f"G06-PREP-FAIL: {error}", file=sys.stderr)
        sys.exit(1)
