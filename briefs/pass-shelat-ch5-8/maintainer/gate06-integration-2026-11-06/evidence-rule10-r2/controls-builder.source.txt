"""Prepare Gate06 Rule-10 controls; never invoke Lean, Git, or a shell.

Run only after build_seals.py has produced a completed seal-manifest.json:
  python3 -I .lake/ps-maintainer/gate06/build_controls.py EVIDENCE_DIRECTORY --root WORKTREE

All Lean files go to ignored .lake scratch. Evidence receives .source.txt
copies and JSON only. Preparation does not establish control sensitivity.
"""

from __future__ import annotations

import argparse
import datetime
import importlib.util
import json
from pathlib import Path
import re
import sys


DEFAULT_MODULE = "TCSlib.Cryptography.Authentication.DLHash"
MATCHER_SOURCE = Path("briefs/pass-shelat-ch5-8/gates/08-shared/evidence/tools/controls_body.lean")
MATCHER_SHA256 = "21503515b1e0a19282a512d59ee2d6d99f6815bbe9a8457a22da43aebb3e3f5a"
REQUIRED = {
    "Complexity.NUPPT.inArg": ("TCSlib.Complexity.Randomized.Closure", False),
    "Complexity.NUPPT.advInput": ("TCSlib.Complexity.Randomized.PPT", False),
    "TCSlib.Cryptography.uexp": ("TCSlib.Cryptography.Foundations.Probability", False),
    "Complexity.polyTimeComputable_iterateFind.match_1":
        ("TCSlib.Complexity.Randomized.Repetition", True),
}
READERS = {
    "Complexity.NUPPT.inArg_eq": "TCSlib.Complexity.Randomized.Closure",
    "Complexity.NUPPT.advInput_eq": "TCSlib.Complexity.Randomized.PPT",
    "TCSlib.Cryptography.uexp_def": "TCSlib.Cryptography.Foundations.Probability",
}
NEGATIVE_BODIES = {
    "InArg": ("Complexity.NUPPT.inArg", """theorem inArgBody (z : List Bool) :
    Complexity.NUPPT.inArg z = Complexity.pairSndD (Complexity.pairFstD (Complexity.pairFstD z)) := rfl
"""),
    "AdvInput": ("Complexity.NUPPT.advInput", """theorem advInputBody (n : ℕ) (y : List Bool) :
    Complexity.NUPPT.advInput n y = Turing.pairEncode (List.replicate n true) y := rfl
"""),
    "Uexp": ("TCSlib.Cryptography.uexp", """theorem uexpBody (f : Fin 3 → ℝ) :
    TCSlib.Cryptography.uexp f = (∑ a, f a) / Fintype.card (Fin 3) := rfl
"""),
    "AnonymousOnly": ("Complexity.NUPPT.inArg", """example (z : List Bool) :
    Complexity.NUPPT.inArg z = Complexity.pairSndD (Complexity.pairFstD (Complexity.pairFstD z)) := rfl
"""),
}
POSITIVE_BODY = """theorem inArgReader (z : List Bool) :
    Complexity.NUPPT.inArg z = Complexity.pairSndD (Complexity.pairFstD (Complexity.pairFstD z)) :=
  Complexity.NUPPT.inArg_eq z

theorem advInputReader (n : ℕ) (y : List Bool) :
    Complexity.NUPPT.advInput n y = Turing.pairEncode (List.replicate n true) y :=
  Complexity.NUPPT.advInput_eq n y

theorem uexpReader (f : Fin 3 → ℝ) :
    TCSlib.Cryptography.uexp f = (∑ a, f a) / Fintype.card (Fin 3) :=
  TCSlib.Cryptography.uexp_def f
"""


class ControlPreparationError(RuntimeError):
    pass


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ControlPreparationError(message)


def load_builder(path: Path):
    # Import definitions only; prevent even Python bytecode-cache writes.
    sys.dont_write_bytecode = True
    spec = importlib.util.spec_from_file_location("gate06_control_seal_builder", path)
    require(spec is not None and spec.loader is not None, "cannot load reviewed seal builder")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def catalog_command(bs, label: str, rows: list[dict], phase: str) -> bytes:
    """Check actual imported Names and collector metadata without changing status.

    The same Array-actual-Name catalog discipline as seal_command is used.
    No Lean.Name is reconstructed from a printed spelling, including matchers.
    """
    entries = ["    (" + ", ".join((bs.lean_string(row["spelling"]), bs.lean_string(row["home"]),
                                      str(row["matcher"]).lower(),
                                      bs.lean_string(row["collector_reducibility"]))) + ")"
               for row in rows]
    reader_entries = ["    (" + bs.lean_string(name) + ", " + bs.lean_string(home) + ")"
                      for name, home in sorted(READERS.items())]
    lines = [f"/- G06-CONTROL-CATALOG {phase} {label} -/", "run_cmd do",
             "  let label : String := " + bs.lean_string(label),
             "  let phase : String := " + bs.lean_string(phase),
             "  let mut requests : Array (String × String × Bool × String) := #[]"]
    for start in range(0, len(entries), bs.REQUEST_CHUNK_SIZE):
        lines += ["  requests := requests ++ #[", ",\n".join(entries[start:start + bs.REQUEST_CHUNK_SIZE]), "  ]"]
    lines += ["  let readers : Array (String × String) := #[", ",\n".join(reader_entries), "  ]",
              "  let env ← Lean.getEnv",
              "  let mut catalog : Std.HashMap String (Array Lean.Name) := {}",
              "  for (n, _) in env.constants.map₁.toList do",
              "    let some mi := env.getModuleIdxFor? n | continue",
              "    unless (`TCSlib).isPrefixOf env.header.moduleNames[mi.toNat]! do continue",
              "    catalog := catalog.insert n.toString (((catalog[n.toString]?).getD #[]).push n)",
              "  let mut verified : Nat := 0",
              "  for (spelling, expectedHome, expectedMatcher, expectedStatus) in requests do",
              "    let ns := (catalog[spelling]?).getD #[]",
              '    unless ns.size == 1 do throwError "G06-CONTROL-HARNESS {label}: absent/ambiguous {spelling}; candidates={ns.size}"',
              "    let n := ns[0]!",
              '    let some mi := env.getModuleIdxFor? n | throwError "G06-CONTROL-HARNESS {label}: no home for {spelling}"',
              "    let home := env.header.moduleNames[mi.toNat]!",
              '    unless home.toString == expectedHome do throwError "G06-CONTROL-HARNESS {label}: wrong home for {spelling}: {home}"',
              '    let some ci := env.find? n | throwError "G06-CONTROL-HARNESS {label}: absent constant {spelling}"',
              '    unless ci.isDefinition do throwError "G06-CONTROL-HARNESS {label}: not a definition {spelling}"',
              '    if isInstanceCore env n then throwError "G06-CONTROL-HARNESS {label}: unexpected instance {spelling}"',
              "    let matcher := (Lean.Meta.Match.Extension.getMatcherInfo? env n).isSome",
              '    unless matcher == expectedMatcher do throwError "G06-CONTROL-HARNESS {label}: matcher metadata differs for {spelling}"',
              "    let status ← Lean.Elab.Command.liftCoreM <| Lean.getReducibilityStatus n",
              "    let statusName : String := match status with",
              '      | .reducible => "reducible"',
              '      | .semireducible => "semireducible"',
              '      | .irreducible => "irreducible"',
              '    unless statusName == expectedStatus do throwError "G06-CONTROL-HARNESS {label}: reducibility metadata differs for {spelling}: {statusName}"',
              "    verified := verified + 1",
              '  unless verified == requests.size do throwError "G06-CONTROL-HARNESS {label}: catalog count mismatch"',
              "  let mut verifiedReaders : Nat := 0",
              "  for (spelling, expectedHome) in readers do",
              "    let ns := (catalog[spelling]?).getD #[]",
              '    unless ns.size == 1 do throwError "G06-CONTROL-HARNESS {label}: absent/ambiguous reader {spelling}"',
              "    let n := ns[0]!",
              '    let some mi := env.getModuleIdxFor? n | throwError "G06-CONTROL-HARNESS {label}: no reader home {spelling}"',
              "    let home := env.header.moduleNames[mi.toNat]!",
              '    unless home.toString == expectedHome do throwError "G06-CONTROL-HARNESS {label}: wrong reader home {spelling}"',
              "    match env.find? n with",
              "    | some (.thmInfo _) => pure ()",
              '    | _ => throwError "G06-CONTROL-HARNESS {label}: reader is not a theorem {spelling}"',
              "    verifiedReaders := verifiedReaders + 1",
              '  unless verifiedReaders == readers.size do throwError "G06-CONTROL-HARNESS {label}: reader count mismatch"',
              '  Lean.logInfo m!"G06-CONTROL-CATALOG label={label} phase={phase} requested={requests.size} verified={verified} readers={verifiedReaders}"', ""]
    return ("\n".join(lines) + "\n").encode()


def assemble(bs, label: str, module: str, rows: list[dict], body: bytes, *, sealed: bool) -> tuple[bytes, dict]:
    prelude = (f"import Lean\nimport {module}\n\nset_option maxHeartbeats 0\n"
               "set_option autoImplicit false\nset_option relaxedAutoImplicit false\n"
               "open Lean Meta Elab Command\nopen Complexity Turing TCSlib.Cryptography\n"
               "open scoped BigOperators\n\n").encode()
    source = prelude + catalog_command(bs, label, rows, "before")
    if sealed:
        source += bs.seal_command(label, rows, end=False)
    source += f'run_cmd Lean.logInfo "G06-CONTROL-BODY-BEGIN {label}"\n\n'.encode()
    source += b"namespace Gate06Sensitivity\n\n"
    start = source.count(b"\n") + 1
    source += body
    require(body.endswith(b"\n"), "control body lacks final newline")
    end = source.count(b"\n")
    rfl_lines = [start + index for index, line in enumerate(body.decode().splitlines()) if ":= rfl" in line]
    source += b"\nend Gate06Sensitivity\n\n"
    source += f'run_cmd Lean.logInfo "G06-CONTROL-BODY-END {label}"\n\n'.encode()
    if sealed:
        source += bs.seal_command(label, rows, end=True)
    else:
        source += catalog_command(bs, label, rows, "after")
    return source, {"start": start, "end": end, "rfl_lines": rfl_lines}


def validate_selected(bs, manifest: dict, module: str, modules: dict, closures: dict, log: str) -> tuple[list[dict], dict]:
    require(module in modules, "selected control import is not an audited math module")
    require(len(manifest.get("probes", [])) == len(modules) == bs.EXPECTED_MODULES,
            "seal manifest does not cover exactly all 51 audited math modules")
    by_module = {record["module"]: record for record in manifest["probes"]}
    require(set(by_module) == set(modules), "duplicate or missing module in seal manifest")
    _, conservative, _ = bs.collector_rows(log, modules, closures)
    record = by_module[module]
    require(record["import_closure"] == closures[module], "control closure differs from audited module closure")
    rows = [conservative[module][name] for name in sorted(conservative[module])]
    require(record["requested_names"] == rows and record["requested_count"] == len(rows),
            "manifest request list is not the completed collector's full conservative closure")
    require(record["term_subset_of_closure"] is True, "missing term/closure coverage assertion")
    for spelling, (home, matcher) in REQUIRED.items():
        require(spelling in conservative[module], f"required control target absent from full closure: {spelling}")
        row = conservative[module][spelling]
        require(row["home"] == home and row["matcher"] is matcher,
                f"control target has wrong home/matcher metadata: {spelling}")
        require(row["collector_reducibility"] != "irreducible",
                f"control target is already irreducible; not a valid unsealed baseline: {spelling}")
    for home in READERS.values():
        require(home in closures[module], f"reader home outside selected import closure: {home}")
    require(record["collector_irreducible_count"] == sum(r["collector_reducibility"] == "irreducible" for r in rows),
            "manifest already-irreducible count differs")
    require(record["collector_active_candidate_count"] == sum(r["collector_reducibility"] != "irreducible" for r in rows),
            "manifest active-candidate count differs")
    return rows, record


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("evidence_directory", type=Path)
    parser.add_argument("--root", type=Path, default=Path.cwd())
    parser.add_argument("--module", default=DEFAULT_MODULE)
    args = parser.parse_args()
    root, evidence = args.root.resolve(), args.evidence_directory.resolve()
    # Fail before imports or any output while collection/preparation is incomplete.
    require((evidence / "seal-manifest.json").is_file(), "no completed seal-manifest.json; no controls prepared")
    require((evidence / "collect1.json").is_file(), "no collector completion JSON; no controls prepared")
    require(not evidence.is_relative_to(root / "TCSlib"), "evidence is inside library sources")
    builder_path = root / ".lake/ps-maintainer/gate06/build_seals.py"
    bs = load_builder(builder_path)
    captured = {}
    manifest = bs.read_json(evidence / "seal-manifest.json", captured)
    require(manifest["status"] == "PREPARED_NOT_RUN", "unrecognized whole-file preparation status")
    require(manifest["root"] == str(root), "control root differs from seal-manifest root")
    require(manifest["evidence_directory"] == str(evidence), "evidence path differs from seal manifest")
    require(bs.sha(builder_path.read_bytes()) == manifest["builder_sha256"], "seal builder changed since manifest")
    require((evidence / "build_seals.py").read_bytes() == builder_path.read_bytes(), "saved seal builder differs")
    for name, digest in manifest["input_sha256"].items():
        require(Path(name).name == name, "unsafe manifest input name")
        raw = (evidence / name).read_bytes()
        require(bs.sha(raw) == digest, f"seal-manifest input changed: {name}")
        captured[name] = raw
    data = {name: bs.read_json(evidence / name, captured) for name in
            ("pins.json", "modules.json", "closures.json", "source-fingerprints.json", "touched.json")}
    pins, modules, closures = (data[name] for name in ("pins.json", "modules.json", "closures.json"))
    require(set(modules) == set(closures) == set(data["touched.json"]), "module metadata keys differ")
    snapshot = manifest["library_verification"]
    require(snapshot["head"] == pins["head"] and snapshot["base"] == pins["base"] and
            snapshot["library_git_tree"] == pins["library_git_tree"] and
            snapshot["source_bytes_equal_head"] is True and snapshot["base_is_ancestor"] is True,
            "seal manifest lacks matching pinned-library verification")
    paths = sorted([p for p in (root / "TCSlib").rglob("*.lean")] + [root / "TCSlib.lean"])
    library = {}
    for path in paths:
        require(path.is_file() and not path.is_symlink(), f"non-ordinary current library file: {path}")
        library[path.relative_to(root).as_posix()] = path.read_bytes()
    content_hash = bs.sha("".join(f"{p}\t{bs.sha(library[p])}\n" for p in sorted(library)).encode())
    require(len(library) == snapshot["library_file_count"] and content_hash == snapshot["library_content_sha256"],
            "current library bytes differ from completed seal preparation")
    for path, digest in data["source-fingerprints.json"].items():
        require(path in library and bs.sha(library[path]) == digest, f"audited fingerprint differs: {path}")
    log, completed, _ = bs.completed_collector(root, evidence, captured, modules, closures)
    require(completed == manifest["collector_result"], "collector completion differs from seal manifest")
    rows, parent_record = validate_selected(bs, manifest, args.module, modules, closures, log)
    original = (root / MATCHER_SOURCE).read_bytes()
    a, b = original.index(b"-- C10 "), original.index(b"-- C11 ")
    matcher = original[a:b]
    require(bs.sha(matcher) == MATCHER_SHA256, "verified Gate08 C10 matcher control changed")
    bodies = {name: (target, text.encode()) for name, (target, text) in NEGATIVE_BODIES.items()}
    bodies["Matcher"] = ("Complexity.polyTimeComputable_iterateFind.match_1", matcher)
    anonymous = bs.blank_comments_strings(bodies["AnonymousOnly"][1].decode())
    require(len(re.findall(r"(?m)^example\b", anonymous)) == 1 and
            re.search(r"\b(?:theorem|lemma|def|instance|structure|inductive|abbrev)\b", anonymous) is None,
            "anonymous-only control contains a stored named declaration")
    scratch, saved = root / bs.SCRATCH_REL / "controls", evidence / "controls"
    output_manifest = {
        "status": "PREPARED_NOT_RUN", "created_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "builder_sha256": bs.sha(Path(__file__).read_bytes()), "seal_builder_sha256": manifest["builder_sha256"],
        "root": str(root), "evidence_directory": str(evidence), "audited_module": args.module,
        "audited_probe_label": parent_record["label"], "import_closure": closures[args.module],
        "seal_manifest_sha256": bs.sha(captured["seal-manifest.json"]),
        "input_sha256": {name: bs.sha(raw) for name, raw in sorted(captured.items())},
        "library_verification": snapshot, "requested_names": rows, "requested_count": len(rows),
        "collector_active_candidate_count": parent_record["collector_active_candidate_count"],
        "collector_irreducible_count": parent_record["collector_irreducible_count"],
        "required_negative_targets": {n: conservative_row for n in REQUIRED
                                      for conservative_row in rows if conservative_row["spelling"] == n},
        "positive_readers": READERS, "matcher_origin": str(MATCHER_SOURCE),
        "matcher_control_sha256": MATCHER_SHA256,
        "lean_processes_started": 0, "git_processes_started": 0,
        "sensitivity_verified": False, "anonymous_sensitivity_verified": False,
        "published_readers_verified": False, "probes": [],
        "expected_totals": {"probes": 11, "unsealed_passes": 5, "sealed_negative_failures": 5,
                            "sealed_positive_passes": 1, "proof_error_diagnostics": 5,
                            "harness_error_diagnostics": 0},
        "acceptance_rule": "Each unsealed negative must pass; each sealed negative must have exactly one error in its body proof region and zero harness errors; the sealed reader file must pass. Require successful catalog checks, full requested/active/already counts, and EOF installed-status verification. Harness/setup failures never establish sensitivity.",
    }
    planned = []
    for case, (target, body) in bodies.items():
        for sealed in (False, True):
            mode = "Sealed" if sealed else "Unsealed"
            label = f"G06Control_{case}_{mode}"
            source, proof_region = assemble(bs, label, args.module, rows, body, sealed=sealed)
            require(len(proof_region["rfl_lines"]) == 1, f"not exactly one rfl proof: {label}")
            probe = scratch / (label + ".lean")
            saved_source = saved / (label + ".source.txt")
            record = {"label": label, "case": case, "mode": mode, "target": target,
                      "anonymous_only": case == "AnonymousOnly", "proof_count": 1,
                      "proof_region": proof_region, "body_sha256": bs.sha(body),
                      "source_sha256": bs.sha(source), "probe_path": str(probe),
                      "probe_module": probe.relative_to(root).with_suffix("").as_posix(),
                      "saved_source": str(saved_source), "status": "PREPARED_NOT_RUN",
                      "expected_exit": "nonzero" if sealed else 0,
                      "expected_error_diagnostics": int(sealed), "expected_harness_errors": 0,
                      "fresh_nonempty_object_required": not sealed,
                      "full_closure_sealed": sealed, "requested_count": len(rows)}
            output_manifest["probes"].append(record)
            planned += [(probe, source), (saved_source, source)]
    label = "G06Control_PublishedReaders_Sealed"
    source, proof_region = assemble(bs, label, args.module, rows, POSITIVE_BODY.encode(), sealed=True)
    require(not proof_region["rfl_lines"], "published-reader control contains an rfl proof")
    probe = scratch / (label + ".lean")
    saved_source = saved / (label + ".source.txt")
    output_manifest["probes"].append({
        "label": label, "case": "PublishedReaders", "mode": "Sealed", "proof_count": 3,
        "proof_region": proof_region, "source_sha256": bs.sha(source), "probe_path": str(probe),
        "probe_module": probe.relative_to(root).with_suffix("").as_posix(), "saved_source": str(saved_source),
        "status": "PREPARED_NOT_RUN", "expected_exit": 0, "expected_error_diagnostics": 0,
        "expected_harness_errors": 0, "fresh_nonempty_object_required": True,
        "full_closure_sealed": True, "requested_count": len(rows), "readers": sorted(READERS),
    })
    planned += [(probe, source), (saved_source, source),
                (evidence / "controls-manifest.json", bs.json_bytes(output_manifest)),
                (evidence / "controls-builder.source.txt", Path(__file__).read_bytes())]
    require(len(output_manifest["probes"]) == 11 and len({p for p, _ in planned}) == len(planned),
            "control probe/output counts differ")
    for path, _ in planned:
        require(not path.exists(), f"refusing to overwrite previous control preparation: {path}")
    # No external process is invoked: revalidate captured source/evidence bytes directly.
    for path, raw in library.items():
        require((root / path).read_bytes() == raw, f"library changed during preparation: {path}")
    for name, raw in captured.items():
        require((evidence / name).read_bytes() == raw, f"evidence changed during preparation: {name}")
    require((root / MATCHER_SOURCE).read_bytes() == original, "matcher control changed during preparation")
    require(bs.sha(builder_path.read_bytes()) == manifest["builder_sha256"], "seal builder changed during preparation")
    for path, content in planned:
        path.parent.mkdir(parents=True, exist_ok=True)
        with path.open("xb") as handle:
            handle.write(content)
    print(json.dumps({"status": "PREPARED_NOT_RUN", "module": args.module, "probes": 11,
                      "requested_count": len(rows), "manifest": str(evidence / "controls-manifest.json"),
                      "lean_processes_started": 0, "git_processes_started": 0}))


if __name__ == "__main__":
    try:
        main()
    except (ControlPreparationError, OSError, ValueError, KeyError, RuntimeError) as error:
        print(f"G06-CONTROL-PREP-FAIL: {error}", file=sys.stderr)
        sys.exit(1)
