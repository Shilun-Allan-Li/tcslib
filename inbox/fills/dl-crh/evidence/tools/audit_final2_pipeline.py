#!/usr/bin/env python3
"""Finish edition final2 serially after its native base controls succeed.

Every Lean check goes through rule10_run.run_one or its existing CLI and hence
scripts/lean_check_tree.sh and the shared-host gate. Run as python3 -I.
"""
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
EDITION = "final2"

def load(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module

def run(*args):
    print("PHASE", *args, flush=True)
    subprocess.run([sys.executable, "-I", *args], cwd=ROOT, check=True)

validation = [json.loads(line) for line in
    (ROOT / "evidence/logs/rule10/final2/controls-base/control-validation.jsonl").read_text().splitlines()]
assert len(validation) == 8 and all(row["passed"] for row in validation), "base pilot controls incomplete"

# Native scan review can proceed in parallel with the remaining serial seals.
for side in ("base", "final"):
    run("evidence/tools/rule10_scan.py", "run", "--edition", EDITION, "--side", side)

P = load(ROOT / "evidence/tools/rule10_prepare.py", "dl_crh_final2_prepare")
R = load(ROOT / "evidence/tools/rule10_run.py", "dl_crh_final2_run")
state = json.loads((ROOT / "evidence/probes/Rule10/base-state.json").read_text())
R.verify_source_snapshot(state, ROOT / state["root"])
manifest = json.loads((ROOT / "evidence/probes/Rule10/final2/base-seal-manifest.json").read_text())
for index, entry in enumerate(manifest["probes"]):
    record = json.loads((ROOT / entry["record"]).read_text())
    result = R.run_one(record["probe_module"], "base", "seals-base", EDITION, record)
    assert result["source_unchanged"] and result["harness_error"] is None
    assert result["mask_verified"] and result["actual_name_components_verified"]
    assert all(e["classification"] == "SOURCE" for e in result["failing_declarations"])
    assert (result["exit_code"] != 0) == bool(result["failing_declarations"]), "native exit/source failure mismatch"
    if index == 0:
        assert entry["owner"] == "TCSlib.Cryptography.Candidates.DiscreteLog" and entry["variant"] == "A"
        # This establishes the full native pilot before adopting the optimized
        # harness for the remaining probes. It compares the completed old run.
        run("evidence/tools/seal_provenance.py")

run("evidence/tools/rule10_run.py", "seals", "--edition", EDITION, "--side", "final")
run("evidence/tools/rule10_controls.py", "run", "--edition", EDITION, "--side", "final")
run("evidence/tools/rule10_summary.py", "--edition", EDITION,
    "--base-census-log", "evidence/logs/rule10/checkpoint1/base-collect/evidence_probes_Rule10_CensusBase.001.log",
    "--final-census-log", "evidence/logs/rule10/final2/final-collect/evidence_probes_CensusFinal.001.log")
print("FINAL2 AUDIT PIPELINE FINISHED; manual review and delivery checks remain", flush=True)
