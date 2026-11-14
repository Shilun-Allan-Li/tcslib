#!/usr/bin/env python3
"""Finish the repaired final snapshot with transparent fixed-baseline reuse.

Run as python3 -I after the repaired sweep. All Lean invocations remain serial
through rule10_run.run_one and scripts/lean_check_tree.sh. A failed binding stops
the pipeline. Previously completed final3 seals are reused only if every one of
the 104 compiled closure objects is byte-identical before/after the sweep.
"""
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
EDITION = "final3"

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def load(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module

def run(*args):
    print("PHASE", *args, flush=True)
    subprocess.run([sys.executable, "-I", *args], cwd=ROOT, check=True)

order = (ROOT / "evidence/final-order.txt").read_text().splitlines()
results = ROOT / "evidence/logs/final-sweep-repaired/results.jsonl"
sweep = [json.loads(line) for line in results.read_text().splitlines()]
assert [r["module"] for r in sweep] == order
assert all(r["exit_code"] == 0 and r["source_unchanged"] for r in sweep)
before = json.loads((ROOT / "evidence/probes/Rule10/final3/pre-sweep-objects.json").read_text())
for row in before["rows"]:
    assert sha(ROOT / (row["module"] + ".lean")) == row["source_sha256"]
    assert sha(ROOT / ".lake/tcslib-check-oleans" / (row["module"] + ".olean")) == row["olean_sha256"], row["module"]
(ROOT / "evidence/probes/Rule10/final3/post-sweep-object-identity.json").write_text(
    json.dumps(dict(status="PASS", all_closure_objects_identical=True, count=len(before["rows"]),
                    pre_sweep_record_sha256=sha(ROOT / "evidence/probes/Rule10/final3/pre-sweep-objects.json"),
                    sweep_results_sha256=sha(results)), indent=2) + "\n")
run("evidence/tools/check_snapshot.py")
run("evidence/tools/admission_delta.py", "--results", "evidence/logs/final-sweep-repaired/results.jsonl",
    "--report", "evidence/admission-delta-repaired.md", "--json", "evidence/admission-delta-repaired.json")
run("evidence/tools/rule10_scan.py", "run", "--edition", EDITION, "--side", "final")

R = load(ROOT / "evidence/tools/rule10_run.py", "dl_crh_final3_run")
state = json.loads((ROOT / "evidence/probes/Rule10/final3/snapshot.json").read_text())
R.verify_source_snapshot(state, ROOT)
R.verify_final_products(state)
manifest = json.loads((ROOT / "evidence/probes/Rule10/final3/final-seal-manifest.json").read_text())
done_path = ROOT / "evidence/logs/rule10/final3/seals-final/results.jsonl"
done = {r["label"]: r for r in (json.loads(line) for line in done_path.read_text().splitlines())}
for entry in manifest["probes"]:
    record = json.loads((ROOT / entry["record"]).read_text())
    prior = done.get(entry["label"])
    if prior is not None:
        assert prior["source_sha256"] == record["probe_sha256"] and prior["source_unchanged"]
        assert sha(ROOT / prior["log"]) == prior["log_sha256"]
        assert prior["exit_code"] == 0 and not prior["errors"] and prior["harness_error"] is None
        assert prior["mask_verified"] and prior["actual_name_components_verified"]
        print("REUSED unchanged same-edition completed seal", entry["label"], flush=True)
        continue
    result = R.run_one(record["probe_module"], "final", "seals-final", EDITION, record)
    assert result["source_unchanged"] and result["harness_error"] is None
    assert result["mask_verified"] and result["actual_name_components_verified"]
    assert result["exit_code"] == 0 and not result["errors"], result["log"]

run("evidence/tools/rule10_controls.py", "run", "--edition", EDITION, "--side", "final")
run("evidence/tools/rule10_summary.py", "--edition", EDITION, "--base-edition", "final2",
    "--base-census-log", "evidence/logs/rule10/checkpoint1/base-collect/evidence_probes_Rule10_CensusBase.001.log",
    "--final-census-log", "evidence/logs/rule10/final3/final-collect/evidence_probes_CensusFinal.001.log")
print("FINAL3 AUDIT PIPELINE FINISHED; manual review/report/delivery remain", flush=True)
