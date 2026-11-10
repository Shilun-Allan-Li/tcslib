"""Check selected modules serially through the campaign's per-module check script."""

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--order", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--oleans", type=Path, required=True)
    args = parser.parse_args()
    output = args.output.resolve()
    oleans = args.oleans.resolve()
    assert output.is_relative_to(ROOT) and oleans.is_relative_to(ROOT)
    assert not (ROOT / ".lake/build/lib/lean").exists(), "Unexpected fallback TCSlib objects."
    output.mkdir(parents=True, exist_ok=True)
    oleans.mkdir(parents=True, exist_ok=True)
    records = []
    env = dict(os.environ, TCSLIB_OLEANS=str(oleans))
    modules = [line.strip() for line in args.order.read_text().splitlines()
               if line.strip() and not line.startswith("#")]
    job = ROOT / ".lake/dyadic-own-job.json"
    for module in modules:
        source = ROOT / (module + ".lean")
        assert source.resolve().is_relative_to(ROOT) and source.is_file(), module
        log = output / (module.replace("/", "-") + ".log")
        started = time.monotonic()
        timestamp = datetime.now(timezone.utc).isoformat()
        with log.open("w") as stream:
            proc = subprocess.Popen(["bash", "scripts/lean_check_tree.sh", module], cwd=ROOT,
                                    env=env, stdout=stream, stderr=subprocess.STDOUT,
                                    start_new_session=True)
            job.write_text(json.dumps(dict(driver_pid=os.getpid(), script_pid=proc.pid,
                                           module=module, status="running", oleans=str(oleans))) + "\n")
            code = proc.wait()
        text = log.read_text()
        row = dict(module=module, started_utc=timestamp,
                   seconds=round(time.monotonic() - started, 3), exit_code=code,
                   error_lines=sum(bool(re.search(r"\berror(?:\([^)]*\))?:", line))
                                   for line in text.splitlines()),
                   admission_warnings=text.count("declaration uses 'sorry'"),
                   source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
                   log=str(log.relative_to(ROOT)),
                   fresh_olean=(oleans / (module + ".olean")).is_file())
        records.append(row)
        (output / "checks.json").write_text(json.dumps(records, indent=2) + "\n")
        job.write_text(json.dumps(dict(driver_pid=os.getpid(), script_pid=proc.pid,
                                       module=module, status="completed", exit_code=code)) + "\n")
        print(json.dumps({key: row[key] for key in
                          ["module", "seconds", "exit_code", "error_lines", "admission_warnings"]}),
              flush=True)
        if code or row["error_lines"] or not row["fresh_olean"]:
            raise SystemExit("Check failed; inspect " + str(log))


if __name__ == "__main__":
    main()
