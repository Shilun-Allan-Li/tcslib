"""Prepare, never run, Gate06 constant-AST harness retries for frozen ordinals 19--51.

Review before invoking:
  python3 -I .lake/ps-maintainer/gate06/repairs/prepare_rule10_harness_retry_v3.py EVIDENCE --root WORKTREE

No Lean, Git, shell, or subprocess invocation occurs. Existing manifests,
probes and evidence are never overwritten. All new results remain NOT_RUN.
"""

from __future__ import annotations

import argparse
import copy
import datetime
import importlib.util
import json
from pathlib import Path
import sys


FROZEN_HEAD = "e9d64158461bfe24ddc88ab885bc4017899b4c16"
FIRST_ORDINAL, LAST_ORDINAL = 19, 51


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def load_module(path: Path, name: str):
    sys.dont_write_bytecode = True
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, "cannot load reviewed builder")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def payload_literal(matrix: list[list[str]], columns: int) -> str:
    """One escaped data literal; never emit one Lean AST node per request row."""
    for row in matrix:
        require(len(row) == columns, "wrong serialized row width")
        require(all(isinstance(field, str) and field and all(ord(c) >= 32 for c in field)
                    for field in row), "empty/control-containing request field")
    require(len({row[0] for row in matrix}) == len(matrix), "duplicate request spelling")
    payload = "\n".join("\t".join(row) for row in matrix)
    decoded = [] if not payload else [line.split("\t") for line in payload.split("\n")]
    require(decoded == matrix, "serialized request rows do not round-trip exactly")
    return json.dumps(payload, ensure_ascii=False)


def request_code(rows: list[dict], *, metadata: bool) -> bytes:
    if metadata:
        require(all(isinstance(row["matcher"], bool) and row["collector_reducibility"] in
                    {"reducible", "semireducible", "irreducible"} for row in rows),
                "invalid control metadata")
        matrix = [[row["spelling"], row["home"], str(row["matcher"]).lower(),
                   row["collector_reducibility"]] for row in rows]
        dtype = "String × String × Bool × String"
    else:
        matrix = [[row["spelling"], row["home"]] for row in rows]
        dtype = "String × String"
    literal = payload_literal(matrix, 4 if metadata else 2)
    lines = ["  let payload : String := " + literal,
             f"  let expectedRequests : Nat := {len(rows)}",
             f"  let mut requests : Array ({dtype}) := #[]",
             r'  let payloadLines := if payload.isEmpty then [] else payload.splitOn "\n"',
             "  for line in payloadLines do",
             r'    match line.splitOn "\t" with']
    if metadata:
        lines += ["    | [spelling, home, matcherText, expectedStatus] =>",
                  '      unless !spelling.isEmpty && !home.isEmpty && !expectedStatus.isEmpty do throwError "G06-HARNESS {label}: empty request field"',
                  "      let matcher : Bool ← match matcherText with",
                  '        | "true" => pure true',
                  '        | "false" => pure false',
                  '        | _ => throwError "G06-HARNESS {label}: malformed matcher field"',
                  "      requests := requests.push (spelling, home, matcher, expectedStatus)"]
    else:
        lines += ["    | [spelling, home] =>",
                  '      unless !spelling.isEmpty && !home.isEmpty do throwError "G06-HARNESS {label}: empty request field"',
                  "      requests := requests.push (spelling, home)"]
    lines += ['    | _ => throwError "G06-HARNESS {label}: malformed serialized request row"',
              '  unless requests.size == expectedRequests do throwError "G06-HARNESS {label}: serialized request count differs: {requests.size} vs {expectedRequests}"']
    return ("\n".join(lines) + "\n").encode()


def replace_request_build(raw: bytes, rows: list[dict], *, metadata: bool) -> bytes:
    dtype = "String × String × Bool × String" if metadata else "String × String"
    start = f"  let mut requests : Array ({dtype}) := #[]\n".encode()
    # Keep the fixed three-reader array verbatim; it does not grow with the seal set.
    stop = ("  let readers : Array" if metadata else "  let env ← Lean.getEnv\n").encode()
    require(raw.count(start) == 1 and raw.count(stop) == 1, "unexpected original command layout")
    a, b = raw.index(start), raw.index(stop)
    require(a < b, "request block boundary order differs")
    replacement = request_code(rows, metadata=metadata)
    result = raw[:a] + replacement + raw[b:]
    require(result[:a] == raw[:a] and result[a+len(replacement):] == raw[b:],
            "code outside request construction changed")
    require(b"requests := requests ++ #[" not in result, "large request literal remains")
    require(b"set_option maxRecDepth" not in result, "unexpected option-budget change")
    return result


def configure_builders(bs, controls):
    old_seal = bs.seal_command
    bs.seal_command = lambda label, rows, *, end: replace_request_build(
        old_seal(label, rows, end=end), rows, metadata=False)
    old_catalog = controls.catalog_command
    controls.catalog_command = lambda builder, label, rows, phase: replace_request_build(
        old_catalog(builder, label, rows, phase), rows, metadata=True)


def restore_original(probe: bytes, insertions: list[dict]) -> bytes:
    recovered = probe
    for addition in reversed(insertions):
        a, n = addition["probe_byte_offset"], addition["byte_count"]
        recovered = recovered[:a] + recovered[a+n:]
    return recovered


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("evidence_directory", type=Path)
    parser.add_argument("--root", type=Path, default=Path.cwd())
    args = parser.parse_args()
    root, evidence = args.root.resolve(), args.evidence_directory.resolve()
    require(not evidence.is_relative_to(root / "TCSlib"), "evidence must be outside library sources")
    require((evidence / "seal-manifest.json").is_file(), "completed original manifest missing")
    require((evidence / "collect1.json").is_file(), "completed original collector missing")
    bs_path = root / ".lake/ps-maintainer/gate06/build_seals.py"
    controls_path = root / ".lake/ps-maintainer/gate06/build_controls.py"
    bs = load_module(bs_path, "gate06_retry_seal_builder")
    controls = load_module(controls_path, "gate06_retry_control_builder")
    captured = {}
    original = bs.read_json(evidence / "seal-manifest.json", captured)
    require(original["status"] == "PREPARED_NOT_RUN", "unrecognized original manifest status")
    require(original["root"] == str(root) and original["evidence_directory"] == str(evidence),
            "root/evidence path differs from original manifest")
    require(original["library_verification"]["head"] == FROZEN_HEAD, "wrong frozen head")
    require(bs.sha(bs_path.read_bytes()) == original["builder_sha256"], "original seal builder changed")
    for name, digest in original["input_sha256"].items():
        require(Path(name).name == name, "unsafe captured evidence name")
        raw = (evidence / name).read_bytes()
        require(bs.sha(raw) == digest, f"original evidence changed: {name}")
        captured[name] = raw
    modules = bs.read_json(evidence / "modules.json", captured)
    closures = bs.read_json(evidence / "closures.json", captured)
    log, completed, _ = bs.completed_collector(root, evidence, captured, modules, closures)
    require(completed == original["collector_result"], "collector completion differs")
    _, conservative, _ = bs.collector_rows(log, modules, closures)
    require(len(original["probes"]) == 51 and
            [p["ordinal"] for p in original["probes"]] == list(range(1, 52)),
            "original probe ordinals differ")
    selected = [p for p in original["probes"] if FIRST_ORDINAL <= p["ordinal"] <= LAST_ORDINAL]
    require(len(selected) == 33, "wrong retry range")
    library = {}
    for path in sorted([*(root / "TCSlib").rglob("*.lean"), root / "TCSlib.lean"]):
        require(path.is_file() and not path.is_symlink(), f"non-ordinary library file: {path}")
        library[path.relative_to(root).as_posix()] = path.read_bytes()
    snapshot = original["library_verification"]
    digest = bs.sha("".join(f"{p}\t{bs.sha(library[p])}\n" for p in sorted(library)).encode())
    require(len(library) == snapshot["library_file_count"] and digest == snapshot["library_content_sha256"],
            "current library bytes differ from the frozen complete snapshot")
    for record in selected:
        module, path = record["module"], record["source"]
        require(module in modules and modules[module] == path, "module/source mismatch")
        require(bs.sha(library[path]) == record["source_sha256"], "raw target source changed")
        require(record["import_closure"] == closures[module], "import closure changed")
        require(record["requested_names"] == [conservative[module][n] for n in sorted(conservative[module])],
                "original request set differs from full collector closure")
        old_probe = Path(record["probe_path"]).read_bytes()
        require(bs.sha(old_probe) == record["probe_sha256"] and old_probe == Path(record["saved_source"]).read_bytes(),
                "original probe bytes differ from evidence")
    old_controls = bs.read_json(evidence / "controls-manifest.json", captured)
    require(old_controls["library_verification"] == snapshot, "control/library snapshot differs")
    require(bs.sha(controls_path.read_bytes()) == old_controls["builder_sha256"], "control builder changed")
    configure_builders(bs, controls)
    created = datetime.datetime.now(datetime.timezone.utc).isoformat()
    result = copy.deepcopy(original)
    result.update({
        "status": "PREPARED_NOT_RUN", "created_utc": created,
        "original_manifest_sha256": bs.sha(captured["seal-manifest.json"]),
        "original_builder_sha256": original["builder_sha256"],
        "builder_sha256": bs.sha(Path(__file__).read_bytes()),
        "attempt_kind": "HARNESS_RETRY_CONSTANT_AST", "ordinal_range": [FIRST_ORDINAL, LAST_ORDINAL],
        "harness_options": {"request_encoding": "newline_tab_runtime_String",
                            "maxRecDepth_changed": False, "uses_scoped_set_option_in": False},
        "probes": [], "lean_processes_started": 0, "git_processes_started": 0,
        "harness_retry_verified": False,
        "limitations": ["No native command was run by this preparation.",
                        "Runtime payload parsing is not native-verified until the retry and controls complete.",
                        "Original raw source bytes and full requested-name rows are unchanged.",
                        "The library snapshot is checked by bytes; this tool does not invoke Git to inspect HEAD."]})
    planned = []
    for old in selected:
        record = copy.deepcopy(old)
        label = old["label"] + "_HarnessV3"
        raw = library[old["source"]]
        probe, additions, line_map = bs.instrument(raw, bs.header(raw), label, old["requested_names"])
        require(restore_original(probe, additions) == raw, "raw source not preserved")
        scratch = root / bs.SCRATCH_REL / "seals-retry-v3" / (label + ".lean")
        saved = evidence / "seals-retry-v3" / (label + ".source.txt")
        record.update({
            "label": label, "original_label": old["label"],
            "original_probe_sha256": old["probe_sha256"], "probe_sha256": bs.sha(probe),
            "probe_path": str(scratch), "probe_module": scratch.relative_to(root).with_suffix("").as_posix(),
            "saved_source": str(saved), "insertions": additions, "source_to_probe_lines": line_map,
            "preamble_lines": next({"start": a["probe_start_line"], "end": a["probe_end_line"]}
                                   for a in additions if a["kind"] == "seal_preamble"),
            "eof_verifier_lines": next({"start": a["probe_start_line"], "end": a["probe_end_line"]}
                                      for a in additions if a["kind"] == "seal_eof_verifier"),
            "status": "PREPARED_NOT_RUN", "runtime_identity_and_installed_status_verified": False,
            "requested_names_unchanged": True, "original_bytes_preserved": True})
        require(record["requested_names"] == old["requested_names"] and
                record["source_sha256"] == old["source_sha256"], "retry coverage/source differs")
        result["probes"].append(record)
        planned += [(scratch, probe), (saved, probe), (saved.with_name(label + ".json"), bs.json_bytes(record))]
    # Prepare sensitivity checks for the same 2,482-name closure as both failed attempts.
    pilot = selected[0]
    require(pilot["module"] == "TCSlib.Cryptography.Randomness.BPPBridge", "unexpected retry pilot")
    rows = pilot["requested_names"]
    in_arg = next((r for r in rows if r["spelling"] == "Complexity.NUPPT.inArg"), None)
    require(in_arg is not None and in_arg["home"] == "TCSlib.Complexity.Randomized.Closure" and
            in_arg["matcher"] is False and in_arg["collector_reducibility"] != "irreducible",
            "negative-control target missing or invalid")
    require(set(controls.READERS.values()).issubset(set(pilot["import_closure"])), "reader homes missing")
    control_manifest = {
        "status": "PREPARED_NOT_RUN", "created_utc": created, "root": str(root),
        "library_verification": copy.deepcopy(snapshot), "audited_module": pilot["module"],
        "original_manifest_sha256": result["original_manifest_sha256"],
        "original_controls_manifest_sha256": bs.sha(captured["controls-manifest.json"]),
        "builder_sha256": result["builder_sha256"], "harness_options": result["harness_options"],
        "requested_names": rows, "requested_count": len(rows),
        "collector_active_candidate_count": pilot["collector_active_candidate_count"],
        "collector_irreducible_count": pilot["collector_irreducible_count"],
        "sensitivity_verified": False, "anonymous_sensitivity_verified": False,
        "published_readers_verified": False, "probes": [],
        "expected_totals": {"probes": 3, "unsealed_passes": 1, "sealed_negative_failures": 1,
                            "sealed_positive_passes": 1, "proof_error_diagnostics": 1,
                            "harness_error_diagnostics": 0}} 
    chosen = [p for p in old_controls["probes"] if p["case"] in {"AnonymousOnly", "PublishedReaders"}]
    require(len(chosen) == 3, "original anonymous/reader controls missing")
    for old in chosen:
        record = copy.deepcopy(old)
        label = old["label"] + "_HarnessV3"
        body = (controls.POSITIVE_BODY if old["case"] == "PublishedReaders" else
                controls.NEGATIVE_BODIES["AnonymousOnly"][1]).encode()
        probe, region = controls.assemble(bs, label, pilot["module"], rows, body,
                                         sealed=old["full_closure_sealed"])
        scratch = root / bs.SCRATCH_REL / "controls-retry-v3" / (label + ".lean")
        saved = evidence / "controls-retry-v3" / (label + ".source.txt")
        record.update({"label": label, "original_label": old["label"], "source_sha256": bs.sha(probe),
                       "body_sha256": bs.sha(body), "proof_region": region, "probe_path": str(scratch),
                       "probe_module": scratch.relative_to(root).with_suffix("").as_posix(),
                       "saved_source": str(saved), "requested_count": len(rows), "status": "PREPARED_NOT_RUN"})
        control_manifest["probes"].append(record)
        planned += [(scratch, probe), (saved, probe)]
    require(result["library_verification"] == original["library_verification"], "library verification changed")
    planned += [(evidence / "seal-retry-v3-manifest.json", bs.json_bytes(result)),
                (evidence / "controls-retry-v3-manifest.json", bs.json_bytes(control_manifest)),
                (evidence / "harness-retry-v3-builder.source.txt", Path(__file__).read_bytes())]
    require(len({p for p, _ in planned}) == len(planned), "duplicate output path")
    for path, _ in planned:
        require(not path.exists(), f"refusing to overwrite existing retry preparation: {path}")
    for path, raw in library.items():
        require((root / path).read_bytes() == raw, f"library changed during preparation: {path}")
    for name, raw in captured.items():
        require((evidence / name).read_bytes() == raw, f"original evidence changed during preparation: {name}")
    require(bs.sha(bs_path.read_bytes()) == original["builder_sha256"], "base seal builder changed")
    require(bs.sha(controls_path.read_bytes()) == old_controls["builder_sha256"], "base control builder changed")
    for path, content in planned:
        path.parent.mkdir(parents=True, exist_ok=True)
        with path.open("xb") as handle:
            handle.write(content)
    print(bs.json_bytes({"status": "PREPARED_NOT_RUN", "probes": 33, "controls": 3,
                         "manifest": str(evidence / "seal-retry-v3-manifest.json"),
                         "lean_processes_started": 0, "git_processes_started": 0}).decode())


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError, RuntimeError) as error:
        print(f"G06-HARNESS-V3-PREP-FAIL: {error}", file=sys.stderr)
        sys.exit(1)
