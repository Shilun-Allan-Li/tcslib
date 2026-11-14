#!/usr/bin/env python3
"""Check the three previously failing whole-file seals on fresh final3 bytes.

Run as python3 -I. All checks use rule10_run's existing serial tree runner.
"""
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
def load(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module
R = load(ROOT / "evidence/tools/rule10_run.py", "dl_crh_repair_run")
state = json.loads((ROOT / "evidence/probes/Rule10/final3/snapshot.json").read_text())
R.verify_source_snapshot(state, ROOT)
R.verify_final_products(state)
manifest = json.loads((ROOT / "evidence/probes/Rule10/final3/final-seal-manifest.json").read_text())
selection = [("TCSlib.Cryptography.Hashing.FromDiscreteLog.Reduction", "A"),
             ("TCSlib.Cryptography.Hashing.FromDiscreteLog.Reduction", "B"),
             ("TCSlib.Cryptography.Hashing.FromDiscreteLog", "B")]
for owner, variant in selection:
    entry, = [e for e in manifest["probes"] if (e["owner"], e["variant"]) == (owner, variant)]
    record = json.loads((ROOT / entry["record"]).read_text())
    result = R.run_one(record["probe_module"], "final", "seals-final", "final3", record)
    assert result["source_unchanged"] and result["harness_error"] is None
    assert result["mask_verified"] and result["actual_name_components_verified"]
    assert result["exit_code"] == 0 and not result["errors"], result["log"]
print("PASS all three repaired full-request seals", flush=True)
