"""Copy only completed, statically checked replays into their gate records."""

from pathlib import Path
import json
import os
import re
import shutil
import subprocess
import sys


records = Path(__file__).resolve().parents[3]
scratch = Path(os.environ["TCSLIB_SCRATCH"])
cases = {"106-sg1-dedup": ("msg1", "wt-sg1", 329, 0),
         "114-natbits-dedup": ("mnb1", "wt-natbits", 344, 0),
         "115-epad-fill": ("mepad1", "wt-epad", 2, -1)}
pattern = re.compile(r"^(\S+) exit=(\d+) errors=(\d+) sorry=(\d+)$", re.M)
base_log = (scratch / "fills/replay/bootstrap-oleans-mac0.log").read_text()
assert base_log.splitlines()[-1] == "# modules=894 failed=0"
base_counts = {m: int(k) for m, _, _, k in pattern.findall(base_log)}
for gate in sys.argv[1:] or cases:
    name, wt, count, expected_delta = cases[gate]
    evidence = records / "campaign/gates" / gate / "evidence/current"
    inputs = json.loads((evidence / "landing/refs.json").read_text())
    commits = {}
    for label, tree in (("head", wt), ("base", "wt-camp")):
        sha = subprocess.check_output(["git", "-C", str(scratch / tree), "rev-parse", "HEAD"], text=True).strip()
        subprocess.run(["git", "-C", str(records), "cat-file", "-e", sha + "^{commit}"], check=True)
        assert sha == inputs[label], (gate, label, sha, inputs[label])
        commits[label] = sha
    replay = scratch / "fills/replay"
    log = (replay / ("replay-" + name + ".log")).read_text()
    assert log.splitlines()[-1] == f"# modules={count} failed=0"
    rows = pattern.findall(log)
    assert len(rows) == count and all(int(st) == int(errors) == 0 for _, st, errors, _ in rows)
    static = (replay / ("replay-" + name + "-static.txt")).read_text()
    assert re.search(rf"modules {count}, mismatches 0, static total \d+\n?$", static)
    assert all(m in base_counts or m.endswith("/NatBits") for m, *_ in rows)
    prior = sum(base_counts.get(m, 0) for m, *_ in rows)
    current = sum(int(k) for _, _, _, k in rows)
    assert current - prior == expected_delta, (gate, prior, current)
    changes = [{"module": m, "base": base_counts.get(m, 0), "head": int(k)}
               for m, _, _, k in rows if base_counts.get(m, 0) != int(k)]
    dest = evidence / "merged-tree"
    dest.mkdir(exist_ok=True)
    for filename in ("down-" + name + ".txt", "replay-" + name + ".sh",
                     "precheck-" + name + ".sh", "replay-" + name + ".log",
                     "replay-" + name + "-static.txt"):
        shutil.copy2(replay / filename, dest / filename)
    receipt = {**commits, "snapshot": "oleans-" + name, "previous_snapshot": "oleans-mac0",
               "modules": count, "failed": 0, "static_mismatches": 0,
               "base_sorry_declarations_in_closure": prior,
               "head_sorry_declarations_in_closure": current,
               "sorry_declaration_delta": current - prior, "sorry_changes": changes}
    (dest / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(gate, count, "passed; sorry declarations", prior, "to", current)
