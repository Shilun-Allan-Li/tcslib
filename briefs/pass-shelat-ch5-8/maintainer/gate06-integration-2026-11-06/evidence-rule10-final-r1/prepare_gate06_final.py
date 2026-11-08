"""Prepare all final seals and all eleven controls after fresh collect1; never starts Lean."""
from pathlib import Path
import argparse, hashlib, importlib.util, json, sys

PREPARER_SHA = "a402e458b32f65edb272276dfb8b6dd9ed59b992024b586b42ccfebe737470f4"
PREPARER = Path(__file__).with_name("prepare_gate06_final_collector.py")

def need(ok, message):
    if not ok:
        raise RuntimeError(message)

def sha(raw):
    return hashlib.sha256(raw).hexdigest()

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--control-module"); args = parser.parse_args()
    need(PREPARER.is_file() and not PREPARER.is_symlink() and sha(PREPARER.read_bytes()) == PREPARER_SHA, "reviewed final preparer changed")
    sys.dont_write_bytecode = True
    spec = importlib.util.spec_from_file_location("gate06_final_preparer", PREPARER)
    need(spec is not None and spec.loader is not None, "cannot load reviewed preparer")
    p = importlib.util.module_from_spec(spec); spec.loader.exec_module(p)
    root, evidence = p.ROOT, p.EVIDENCE
    prep_raw = (evidence / "final-preparation.json").read_bytes(); prep = json.loads(prep_raw)
    need(prep["status"] == "COLLECTOR_PREPARED_NOT_RUN" and prep["root"] == str(root) and prep["evidence_directory"] == str(evidence), "wrong final preparation")
    need(prep["scratch_relative"] == p.SCRATCH_REL.as_posix() and prep["preparer_source_sha256"] == PREPARER_SHA, "preparer configuration differs")
    need((evidence / "prepare_gate06_final_collector.py").read_bytes() == PREPARER.read_bytes(), "saved preparer differs")
    need(prep["tool_input_sha256"] == p.TOOL_HASHES, "preparer tool pins differ")
    raw_tools = p.tool_bytes()
    for name, raw in raw_tools.items(): need((evidence / "tool-inputs" / p.saved_tool_name(name)).read_bytes() == raw, "saved tool differs: " + name)
    need(set(prep["input_sha256"]) == {"pins.json", "modules.json", "closures.json", "source-fingerprints.json", "touched.json", "Collect.source.txt"}, "prepared input set differs")
    for name, digest in prep["input_sha256"].items():
        need(Path(name).name == name and sha((evidence / name).read_bytes()) == digest, "prepared input changed: " + name)
    for name in ("seal-manifest.json", "controls-manifest.json", "final-adapter.json", "prepare_gate06_final.py"):
        need(not (evidence / name).exists(), "refusing existing final output: " + name)
    bs = p.load_tool("build_seals.py", "gate06_final_seal_builder")
    cb = p.load_tool("build_controls.py", "gate06_final_control_builder")
    v3 = p.load_tool("request_payload_adapter.py", "gate06_final_request_payload")
    data = {name: json.loads((evidence / name).read_bytes()) for name in ("pins.json", "modules.json", "closures.json", "source-fingerprints.json", "touched.json")}
    pins, modules, closures = (data[name] for name in ("pins.json", "modules.json", "closures.json"))
    library, snapshot = bs.library_snapshot(root, pins)
    derived, derived_closures, fingerprints, excluded = p.derive_scope(bs, library, pins["base"], pins["head"])
    need(derived == modules and derived_closures == closures and fingerprints == data["source-fingerprints.json"] and excluded == pins["excluded_import_option_only_files"], "fresh base/head scope differs")
    count = len(derived)
    need(count == prep["expected_math_modules"] == pins["audited_math_modules"] and sorted(modules) == prep["modules"] and snapshot == prep["library_verification"], "scope/library pins differ")
    bs.EXPECTED_MODULES = count; bs.SCRATCH_REL = p.SCRATCH_REL
    bs.validate_metadata(root, pins, modules, closures, fingerprints, data["touched.json"], library)
    need(p.collector_source(raw_tools, modules, closures) == (evidence / "Collect.source.txt").read_bytes(), "collector body differs from reviewed construction")
    captured = {}; log, _, _ = bs.completed_collector(root, evidence, captured, modules, closures)
    _, conservative, _ = bs.collector_rows(log, modules, closures)
    candidates = [m for m in sorted(modules) if set(cb.READERS.values()) <= set(closures[m]) and all(
        n in conservative[m] and conservative[m][n]["home"] == home and conservative[m][n]["matcher"] is matcher and conservative[m][n]["collector_reducibility"] != "irreducible"
        for n, (home, matcher) in cb.REQUIRED.items())]
    need(candidates, "no final audited closure supports the existing complete controls")
    chosen = args.control_module or (cb.DEFAULT_MODULE if cb.DEFAULT_MODULE in candidates else candidates[0])
    need(chosen in candidates, "requested control module lacks required targets/readers")
    v3.configure_builders(bs, cb)
    cb.load_builder = lambda _path: bs
    old_argv = sys.argv[:]
    try:
        sys.argv = [str(p.TOOL_PATHS["build_seals.py"]), str(evidence), "--root", str(root)]; bs.main()
        sys.argv = [str(p.TOOL_PATHS["build_controls.py"]), str(evidence), "--root", str(root), "--module", chosen]; cb.main()
    finally:
        sys.argv = old_argv
    seal_raw = (evidence / "seal-manifest.json").read_bytes(); seals = json.loads(seal_raw)
    control_raw = (evidence / "controls-manifest.json").read_bytes(); controls = json.loads(control_raw)
    need(len(seals["probes"]) == count and {v["module"] for v in seals["probes"]} == set(modules), "incomplete final seals")
    need(len(controls["probes"]) == controls["expected_totals"]["probes"] == 11 and controls["seal_manifest_sha256"] == sha(seal_raw), "incomplete/unbound eleven controls")
    need(bs.library_snapshot(root, pins) == (library, snapshot) and p.tool_bytes() == raw_tools, "sources/tools changed during preparation")
    need((evidence / "final-preparation.json").read_bytes() == prep_raw, "preparation record changed")
    for name, digest in prep["input_sha256"].items(): need(sha((evidence / name).read_bytes()) == digest, "prepared input changed during build")
    for name, raw in captured.items(): need((evidence / name).read_bytes() == raw, "collector evidence changed during build")
    self_raw = Path(__file__).read_bytes()
    result = {"status": "PREPARED_NOT_RUN", "root": str(root), "evidence_directory": str(evidence),
        "base": pins["base"], "head": pins["head"], "expected_math_modules": count, "modules": sorted(modules),
        "scratch_relative": p.SCRATCH_REL.as_posix(), "controls_module": chosen,
        "source_sha256": sha(self_raw), "preparer_source_sha256": PREPARER_SHA,
        "final_preparation_sha256": sha(prep_raw), "seal_manifest_sha256": sha(seal_raw), "controls_manifest_sha256": sha(control_raw),
        "collector_result_sha256": sha((evidence / "collect1.json").read_bytes()),
        "tool_input_sha256": {n: p.TOOL_HASHES[n] for n in ("build_seals.py", "build_controls.py", "request_payload_adapter.py")},
        "request_encoding": "constant-AST newline/tab String parsed at runtime", "proof_budgets_changed": False,
        "coverage_exclusions_added": False, "library_verification": snapshot,
        "runtime_verified": False, "limit": "Fresh preparation only. Root must run all final probes/controls and reconcile every result."}
    p.write_new(evidence / "prepare_gate06_final.py", self_raw)
    p.write_new(evidence / "final-adapter.json", p.encoded(result))
    print(json.dumps({"status": result["status"], "modules": count, "controls": 11, "adapter": str(evidence / "final-adapter.json")}), flush=True)

if __name__ == "__main__":
    main()
