#!/usr/bin/env python3
"""Run serialized, slotted module checks and retain all raw evidence."""
import argparse
import datetime
import json
import os
from pathlib import Path
import re
import subprocess
import sys

parser = argparse.ArgumentParser()
parser.add_argument("--phase", required=True)
parser.add_argument("--order")
parser.add_argument("--continue-on-error", action="store_true")
parser.add_argument("modules", nargs="*")
args = parser.parse_args()
modules = args.modules
if args.order:
    modules += [x.strip() for x in Path(args.order).read_text().splitlines() if x.strip()]
dest = Path("evidence/logs") / args.phase
dest.mkdir(parents=True, exist_ok=True)
env = os.environ.copy()
env["LEAN_SLOT_TAG"] = "sc-garble"
any_failure = False
for module in modules:
    path = dest / (module.replace("/", "__") + ".log")
    path.with_suffix(".source.lean").write_bytes(Path(module + ".lean").read_bytes())
    start = datetime.datetime.now(datetime.timezone.utc).isoformat()
    print("START", start, module, flush=True)
    with path.open("w") as log:
        log.write("START " + start + " " + module + "\n")
        log.flush()
        result = subprocess.run([
            "/private/tmp/sc-garble-runtime/lean-slot.sh", "/usr/bin/time", "-l",
            "bash", "scripts/lean_check_tree.sh", module,
        ], stdout=log, stderr=subprocess.STDOUT, env=env)
        end = datetime.datetime.now(datetime.timezone.utc).isoformat()
        log.write("END " + end + " EXIT " + str(result.returncode) + "\n")
    raw = path.read_text()
    errors = len(re.findall(r"^\S+\.lean:\d+:\d+: error[:(]", raw, re.M))
    record = dict(module=module, phase=args.phase, start=start, end=end,
                  exit=result.returncode, errors=errors,
                  sorries=len(re.findall("declaration uses 'sorry'", raw)), log=str(path))
    with (dest / "results.jsonl").open("a") as records:
        records.write(json.dumps(record) + "\n")
    print("END", module, "exit", result.returncode, "errors", errors, flush=True)
    if result.returncode or errors:
        print(raw[-8000:])
        any_failure = True
        if not args.continue_on_error:
            sys.exit(1)
if any_failure:
    sys.exit(1)
