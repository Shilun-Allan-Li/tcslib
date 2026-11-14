#!/usr/bin/env python3
"""Run the required audits serially only after the complete sweep succeeds.

Run as python3 -I. Every Lean call is delegated to the original single-module
runner and shared-host gate. A failing prerequisite stops the pipeline.
"""
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
EDITION = "final1"

def run(*args):
    print("PHASE", *args, flush=True)
    subprocess.run([sys.executable, "-I", *args], cwd=ROOT, check=True)

order = (ROOT / "evidence/final-order.txt").read_text().splitlines()
while True:
    rows = [json.loads(line) for line in
            (ROOT / "evidence/logs/final-sweep/results.jsonl").read_text().splitlines()]
    assert all(r["exit_code"] == 0 and r["source_unchanged"] for r in rows), "sweep failure; skip dependent audits"
    if len(rows) >= len(order) or "--wait-for-sweep" not in sys.argv:
        break
    time.sleep(5)
assert [r["module"] for r in rows] == order, "full sweep not complete in exact order"
for row in rows:
    assert row["exit_code"] == 0 and row["source_unchanged"], row["module"]
    assert hashlib.sha256((ROOT / (row["module"] + ".lean")).read_bytes()).hexdigest() == row["source_sha256"]
run("evidence/tools/check_snapshot.py")
run("evidence/tools/admission_delta.py")
run("evidence/tools/rule10_run.py", "final-collect", "--edition", EDITION)
run("evidence/tools/rule10_prepare.py", "seals", "--edition", EDITION, "--side", "final",
    "--collector-log", "evidence/logs/rule10/final1/final-collect/evidence_probes_Rule10_final1_CollectFinal.001.log")
run("evidence/tools/rule10_controls.py", "prepare", "--edition", EDITION, "--side", "final")
for side in ("base", "final"):
    run("evidence/tools/rule10_run.py", "seals", "--edition", EDITION, "--side", side)
for side in ("base", "final"):
    run("evidence/tools/rule10_controls.py", "run", "--edition", EDITION, "--side", side)
for side in ("base", "final"):
    run("evidence/tools/rule10_scan.py", "run", "--edition", EDITION, "--side", side)
run("evidence/tools/rule10_summary.py", "--edition", EDITION,
    "--base-census-log", "evidence/logs/rule10/checkpoint1/base-collect/evidence_probes_Rule10_CensusBase.001.log",
    "--final-census-log", "evidence/logs/rule10/final1/final-collect/evidence_probes_CensusFinal.001.log")
print("AUDIT PIPELINE FINISHED; manual explicit-scan and delivery review remain", flush=True)
