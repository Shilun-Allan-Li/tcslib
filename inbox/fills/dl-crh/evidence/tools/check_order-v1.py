#!/usr/bin/env python3
"""Check a supplied order serially through lean_check_tree.sh, with raw logs.

Use python3 -I; the live process gate enforces the user's three-job launch cap.
"""
import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import subprocess

parser = argparse.ArgumentParser()
parser.add_argument("order", type=Path)
parser.add_argument("label")
args = parser.parse_args()
logdir = Path("evidence/logs") / args.label
logdir.mkdir(parents=True, exist_ok=True)

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

for module in args.order.read_text().splitlines():
    module = module.strip()
    if not module:
        continue
    stem = module.replace("/", "_")
    attempt = len(list(logdir.glob(stem + ".*.log"))) + 1
    log = logdir / f"{stem}.{attempt:03d}.log"
    source = Path(module + ".lean")
    start = datetime.datetime.now(datetime.timezone.utc).isoformat()
    print("CHECK", module, "start", start, flush=True)
    with log.open("wb") as output:
        env = os.environ.copy()
        env["PATH"] = str(Path("evidence/tools/timed-bin").resolve()) + os.pathsep + env["PATH"]
        result = subprocess.run(
            ["bash", "evidence/tools/wait_lean_slot.sh", "bash", "scripts/lean_check_tree.sh", module],
            stdout=output, stderr=subprocess.STDOUT, env=env,
        )
    end = datetime.datetime.now(datetime.timezone.utc).isoformat()
    obj = Path(".lake/tcslib-check-oleans") / (module + ".olean")
    record = dict(module=module, source_sha256=sha(source), start=start, end=end,
                  exit_code=result.returncode, log=str(log), log_sha256=sha(log),
                  olean_sha256=sha(obj) if obj.exists() else None)
    with (logdir / "results.jsonl").open("a") as records:
        records.write(json.dumps(record) + "\n")
    print("RESULT", module, result.returncode, "end", end, flush=True)
    if result.returncode:
        print(log.read_text(errors="replace"), flush=True)
        raise SystemExit(result.returncode)
