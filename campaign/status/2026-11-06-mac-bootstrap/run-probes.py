"""Run inspected .lean.txt probes only through the campaign's leanelab wrapper.

Usage: run-probes.py GATE WORKTREE SNAPSHOT RELATIVE-PROBE:EXPECTED-EXIT [...]
Each probe gets a pinned input checksum, unmodified output plus an exit line,
and a run receipt. A failed expectation stops the queue. leanelab owns the slots.
"""

from pathlib import Path
import hashlib
import json
import os
import shutil
import subprocess
import sys


records = Path(__file__).resolve().parents[3]
scratch = Path(os.environ["TCSLIB_SCRATCH"])
gate, worktree, snapshot, *probes = sys.argv[1:]
evidence = records / "campaign/gates" / gate / "evidence/current"
wt, snap = scratch / worktree, scratch / snapshot
sha = subprocess.check_output(["git", "-C", str(wt), "rev-parse", "HEAD"], text=True).strip()
subprocess.run(["git", "-C", str(wt), "cat-file", "-e", sha + "^{commit}"], check=True)
assert not subprocess.check_output(["git", "-C", str(wt), "status", "--porcelain"], text=True)
inputs = json.loads((evidence / "landing/refs.json").read_text())
assert sha == inputs["head"]
probe_root = scratch / "gate-probes" / gate / sha
probe_root.mkdir(parents=True, exist_ok=True)
for item in probes:
    relative, expected = item.rsplit(":", 1)
    source = evidence / relative
    assert source.name.endswith(".lean.txt")
    imports = [line.removeprefix("import ").replace(".", "/")
               for line in source.read_text().splitlines() if line.startswith("import TCSlib.")]
    for module in imports:
        assert (snap / (module + ".olean")).is_file(), module
    dest = probe_root / relative.removesuffix(".txt")
    dest.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(source, dest)
    log = source.with_name(source.name.removesuffix(".lean.txt") + ".out")
    probe_env = os.environ.copy()
    probe_env.setdefault("TCSLIB_LEAN_SLOTS", "3")
    with log.open("w") as output:
        result = subprocess.run(
            ["bash", str(records / "devtools/seyoon/leanelab.sh"), str(wt), str(snap), str(dest)],
            stdout=output, stderr=subprocess.STDOUT, env=probe_env)
        output.write(f"\nexit={result.returncode}\n")
    receipt = {"head": sha, "snapshot": snapshot, "probe": relative,
               "input_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
               "imports": imports, "exit": result.returncode, "expected_exit": int(expected)}
    source.with_name(source.name.removesuffix(".lean.txt") + "-run.json").write_text(
        json.dumps(receipt, indent=2) + "\n")
    print(gate, relative, "exit", result.returncode, "expected", expected, flush=True)
    if result.returncode != int(expected):
        raise SystemExit(1)
