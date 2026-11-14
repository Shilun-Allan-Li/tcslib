"""Run prepared ext-nosrc probes one module per lean_check_tree.sh invocation.

This driver is prepared for the root worker and is not run by the preparation
agent. Usage, from the isolated fill checkout:

  python3 -I evidence/tools/run_rule10.py census base
  python3 -I evidence/tools/run_rule10.py seals base
  python3 -I evidence/tools/run_rule10.py census final
  python3 -I evidence/tools/run_rule10.py seals final

Use --tree PATH to select the already bootstrapped single olean tree. No Lake
command, dependency fetch, direct Lean invocation or subprocess timeout occurs.
Failed source seals are collected rather than stopping the remaining survey;
an invalid harness stops immediately. Never run this concurrently with another
writer to the same olean tree. The root worker controls the host's Lean count.
"""

from __future__ import annotations

import argparse
import datetime
import hashlib
import json
import os
import runpy
from pathlib import Path
import re
import subprocess
import sys
import time


ERROR = re.compile(r"^.*?\.lean:(\d+):(\d+): error(?:\([^\n)]*\))?:", re.M)


def digest(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def save_new(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("x") as stream:
        json.dump(value, stream, indent=2, ensure_ascii=False)
        stream.write("\n")


def parse_errors(text: str, line_map: list[dict] | None) -> list[dict]:
    reverse = None if line_map is None else {r["probe_line"]: r["source_line"] for r in line_map}
    result = []
    for match in ERROR.finditer(text):
        line = int(match[1])
        result.append({"probe_line": line, "column": int(match[2]),
                       "source_line": line if reverse is None else reverse.get(line)})
    return result


def verify_harness(text: str, row: dict) -> str | None:
    expected = row.get("requests")
    if expected is None:
        return None
    # Unsealed controls deliberately have neither installation nor EOF harness.
    if row["label"].endswith("Unsealed"):
        assert not expected
        return None
    label = row["label"]
    for phase in ("install", "eof"):
        marker = f"FILL_SEAL_DONE {label} {phase} {len(expected)} {len(expected)}"
        if text.count(marker) != 1:
            return f"missing/repeated {phase} completion marker"
    rows = []
    for line in text.splitlines():
        if "FILL_SEAL_NAME " in line:
            rows.append(json.loads(line.split("FILL_SEAL_NAME ", 1)[1]))
    for phase in ("install", "eof"):
        got = [(r["name"], r["home"]) for r in rows if r["label"] == label and r["phase"] == phase]
        want = [(r["name"], r["home"]) for r in expected]
        if got != want:
            return f"{phase} actual name/home sequence differs from requests"
    if "FILL-HARNESS" in text:
        return "harness diagnostic"
    return None


def run_one(area: Path, row: dict, tree: Path) -> dict:
    module = row["module"]
    source = Path(module + ".lean")
    before = source.read_bytes()
    assert digest(before) == row["probe_sha256"]
    log = area / "logs" / (row["label"] + ".log")
    result_path = log.with_suffix(".json")
    log.parent.mkdir(parents=True, exist_ok=True)
    assert not result_path.exists(), "prior attempt must be preserved"
    env = os.environ.copy()
    env["TCSLIB_OLEANS"] = str(tree)
    native_time = ["/usr/bin/time", "-l" if sys.platform == "darwin" else "-v"]
    command = [*native_time, "bash", "scripts/lean_check_tree.sh", module]
    runpy.run_path('evidence/tools/resource_gate.py')['wait_for_slot']()
    start = datetime.datetime.now(datetime.timezone.utc).isoformat()
    tick = time.monotonic()
    with log.open("xb") as stream:
        stream.write(("START " + start + "\nSOURCE_SHA256 " + digest(before) + "\n").encode())
        stream.flush()
        rc = subprocess.call(command, env=env, stdout=stream, stderr=subprocess.STDOUT)
        end = datetime.datetime.now(datetime.timezone.utc).isoformat()
        stream.write((f"\nEND {end} RC {rc}\n").encode())
    raw_log = log.read_bytes()
    text = raw_log.decode()
    errors = parse_errors(text, row.get("line_map"))
    object_path = tree / (module + ".olean")
    fresh = object_path.is_file() and object_path.stat().st_size > 0
    unchanged = source.read_bytes() == before
    problem = verify_harness(text, row)
    if any(e["source_line"] is None for e in errors):
        problem = "error in inserted instrumentation"
    if not unchanged:
        problem = "probe source changed during check"
    if rc == 0 and (errors or not fresh):
        problem = "success status lacks fresh object or contains error diagnostics"
    if rc != 0 and not errors:
        problem = "failed without source error diagnostic"
    record = {**row, "start_utc": start, "end_utc": end,
              "seconds": round(time.monotonic() - tick, 3), "command": command,
              "olean_tree": str(tree), "rc": rc, "errors": errors,
              "fresh_nonempty_object": fresh, "source_unchanged": unchanged,
              "source_sha256": digest(before), "log": str(log),
              "log_sha256": digest(raw_log), "valid_harness": problem is None,
              "problem": problem,
              "meets_expected_error_count": len(errors) == row.get("expected_errors", 0)}
    save_new(result_path, record)
    print(f'{row["label"]}: rc={rc}, errors={len(errors)}, valid={problem is None}', flush=True)
    if "error: failed to locate application" in text:
        raise RuntimeError("E-RES: failed to locate application; no workaround permitted")
    if problem:
        raise RuntimeError("invalid harness: " + problem)
    return record


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("stage", choices=("census", "seals"))
    parser.add_argument("side", choices=("base", "final"))
    parser.add_argument("--tree", type=Path, default=Path(".lake/tcslib-check-oleans"))
    parser.add_argument("--attempt", help="fresh evidence suffix, e.g. r2; preserves prior areas")
    args = parser.parse_args()
    if args.attempt is not None and not re.fullmatch(r"[a-z][a-z0-9_-]*", args.attempt):
        raise ValueError("attempt must be a short lowercase identifier such as r2")
    area = Path("evidence/rule10") / (args.side if args.attempt is None else args.side + "-" + args.attempt)
    tree = args.tree.resolve()
    assert tree.is_dir(), "bootstrap the tree before running probes"
    init = json.loads((area / "init.json").read_bytes())
    assert init["side"] == args.side and init.get("attempt") == args.attempt
    if args.stage == "census":
        rows = []
        if args.side == "base":
            module = area / "probes/BaseExtraction"
            rows.append({"label": "BaseExtraction", "module": module.as_posix(), "expected_errors": 0,
                         "probe_sha256": digest(module.with_suffix(".lean").read_bytes())})
        rows.append({"label": "Census", "module": init["census_module"], "expected_errors": 0,
                     "probe_sha256": init["census_source_sha256"]})
    else:
        manifest = json.loads((area / "manifest.json").read_bytes())
        rows = manifest["controls"] + manifest["seals"]
    results = []
    result_lines = area / (args.stage + "-results.jsonl")
    assert not result_lines.exists(), "prior survey must be preserved"
    with result_lines.open("x") as stream:
        for row in rows:
            record = run_one(area, row, tree)
            stream.write(json.dumps(record, ensure_ascii=False) + "\n")
            stream.flush()
            results.append(record)
            if args.stage == "census" and (record["rc"] or record["errors"]):
                raise RuntimeError("census prerequisite failed; no dependent check is permitted")
    save_new(area / (args.stage + "-results.json"), {
        "stage": args.stage, "side": args.side, "results": results,
        "all_valid_harnesses": all(r["valid_harness"] for r in results),
        "all_expected_error_counts": all(r["meets_expected_error_count"] for r in results),
        "raw_results_sha256": digest(result_lines.read_bytes())})
    if any(not r["meets_expected_error_count"] for r in results):
        raise SystemExit(1)


if __name__ == "__main__":
    main()
