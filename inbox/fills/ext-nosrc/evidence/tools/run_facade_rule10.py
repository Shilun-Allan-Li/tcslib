"""Run facade-only Rule 10 probes, reusing the existing capped module driver.

Root worker only, after the full downstream bootstrap/sweep. Usage:
  python3 -I evidence/tools/run_facade_rule10.py census base
  python3 -I evidence/tools/run_facade_rule10.py seals base
  python3 -I evidence/tools/run_facade_rule10.py census final
  python3 -I evidence/tools/run_facade_rule10.py seals final

Optional --tree selects the single already-bootstrapped olean tree. No Lake,
direct Lean invocation or check timeout is added. Existing evidence is untouched.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import runpy


shared_path = Path("evidence/tools/run_rule10.py")
shared = runpy.run_path(str(shared_path), run_name="facade_rule10_driver_shared")


def sha(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("stage", choices=("census", "seals"))
    parser.add_argument("side", choices=("base", "final"))
    parser.add_argument("--tree", type=Path, default=Path(".lake/tcslib-check-oleans"))
    args = parser.parse_args()
    area = Path("evidence/rule10/facade-" + args.side)
    tree = args.tree.resolve()
    assert tree.is_dir()
    config = json.loads((area / "init.json").read_bytes())
    assert config["side"] == args.side
    if args.stage == "census":
        rows = []
        if args.side == "base":
            assert (tree / "evidence/rule10/base-r2/probes/BaseExtraction.olean").is_file(), "base Extraction snapshot is a prerequisite"
            module = config["snapshot_module"]
            rows.append({"label": "BaseFacade", "module": module, "expected_errors": 0,
                         "probe_sha256": sha(Path(module + ".lean").read_bytes())})
        else:
            assert (tree / "TCSlib/Cryptography/Randomness.olean").is_file(), "check the final facade in the downstream sweep first"
        rows.append({"label": "Census", "module": config["census_module"], "expected_errors": 0,
                     "probe_sha256": config["census_source_sha256"]})
    else:
        manifest = json.loads((area / "manifest.json").read_bytes())
        assert not manifest["controls"] and len(manifest["verified_reused_controls"]) == 11
        rows = manifest["seals"]
        assert len(rows) == 2
    target = area / (args.stage + "-results.jsonl")
    results = []
    with target.open("x") as stream:
        for row in rows:
            result = shared["run_one"](area, row, tree)
            stream.write(json.dumps(result, ensure_ascii=False) + "\n")
            stream.flush()
            results.append(result)
            if args.stage == "census" and (result["rc"] or result["errors"]):
                raise RuntimeError("facade census prerequisite failed; skip dependent seals")
    shared["save_new"](area / (args.stage + "-results.json"), {
        "side": args.side, "stage": args.stage, "results": results,
        "driver_sha256": sha(Path(__file__).read_bytes()),
        "shared_driver_sha256": sha(shared_path.read_bytes()),
        "raw_results_sha256": sha(target.read_bytes()),
        "all_valid_harnesses": all(r["valid_harness"] for r in results),
        "all_expected_error_counts": all(r["meets_expected_error_count"] for r in results)})
    if any(not r["meets_expected_error_count"] for r in results):
        raise SystemExit(1)


if __name__ == "__main__":
    main()
