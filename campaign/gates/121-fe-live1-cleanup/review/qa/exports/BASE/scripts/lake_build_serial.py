#!/usr/bin/env python3
"""
Serial `lake build`, one module per invocation in import-topological order, so that at
most one `lean` process runs at a time (this Lake has no jobs limit).  Restartable: Lake
skips modules whose .olean is up to date.

    python3 scripts/lake_build_serial.py --area LearningTheory --area CommunicationComplexity [TCSlib.lean]
"""
from __future__ import annotations
import argparse, re, subprocess, sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
from policy_build import ROOT, module_name, topo  # noqa: E402

ap = argparse.ArgumentParser()
ap.add_argument("--area", action="append", default=[])
ap.add_argument("files", nargs="*")
a = ap.parse_args()
files = [Path(f) for f in a.files]
for ar in a.area:
    files += sorted((ROOT / "TCSlib" / ar).rglob("*.lean"))
bad = 0
for f in topo(files):
    mod = module_name(f)
    p = subprocess.run(["lake", "build", mod], cwd=ROOT, capture_output=True, text=True)
    log = p.stdout + p.stderr
    # Lean diagnostics look like `path:line:col: error: …`; `error:` also opens Lake's own
    # failure lines.  (A bare "error" substring would match names like `distributionalError`.)
    errs = [l for l in log.splitlines() if re.search(r"(^|\s)error:", l)]
    sorries = [l for l in log.splitlines() if "declaration uses 'sorry'" in l]
    ok = p.returncode == 0 and not errs
    print(f"[{'OK ' if ok else 'ERR'}] {mod:72s} {(errs[0][:160] if errs else '')}{' SORRY' if sorries else ''}", flush=True)
    if not ok:
        bad += 1
        print(log[-3000:])
        break
print(f"\n{'ALL OK' if not bad else 'FAILED'}: {len(files)} modules")
sys.exit(1 if bad else 0)
