"""Wait for the complete Mac bootstrap, then replay the three pushed PR heads.

No replay starts before the bootstrap's successful final line. Git mutations
and prechecks are sequential; independent replays run under slotrun's two slots.
The scratch copy of mk-next.sh uses Codex attribution, recorded in setup.md.
"""

from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import os
import re
import subprocess
import time


scratch = Path(os.environ["TCSLIB_SCRATCH"])
records = Path(__file__).resolve().parents[3]
log = scratch / "fills/replay/bootstrap-oleans-mac0.log"
while True:
    lines = log.read_text().splitlines()
    if lines and re.fullmatch(r"# modules=\d+ failed=\d+", lines[-1]):
        assert lines[-1] == "# modules=894 failed=0", lines[-1]
        break
    holder = scratch / "locks/lean-slot-1/pid"
    assert holder.exists(), "Bootstrap stopped without a successful final line"
    os.kill(int(holder.read_text()), 0)
    time.sleep(10)

base = subprocess.check_output(
    ["git", "-C", str(scratch / "wt-camp"), "rev-parse", "HEAD"], text=True).strip()
subprocess.run(["git", "-C", str(records), "cat-file", "-e", base + "^{commit}"], check=True)
assert f" at {base} " in lines[0], lines[0]
print("Bootstrap passed; generating three replay prechecks.", flush=True)
cases = [
    ("mepad1", "wt-epad", "lean/epad-padding-fill", 1, "E-PAD #228"),
    ("msg1", "wt-sg1", "lean/dedup-sg1", 4, "SG-1 #215"),
    ("mnb1", "wt-natbits", "lean/dedup-natbits", 22, "NatBits #222"),
]
for name, wt, branch, count, label in cases:
    changed = subprocess.check_output(
        ["git", "-C", str(scratch / wt), "diff", "--name-only",
         "origin/complexity/arora-barak-ch3-4...HEAD", "--", "*.lean"], text=True).splitlines()
    assert len(changed) == count, (name, changed)
    subprocess.run(
        ["bash", str(scratch / "tools/mk-next.sh"), name, wt, branch, base,
         "oleans-mac0", str(log), "oleans-" + name,
         "complete Mac campaign bootstrap", label, str(count)], check=True)


def replay(case: tuple) -> tuple[str, int]:
    name = case[0]
    print("START", name, flush=True)
    result = subprocess.run(
        ["bash", str(scratch / "api/slotrun.sh"), "bash",
         str(scratch / "fills/replay" / ("replay-" + name + ".sh"))])
    print("FINISH", name, "exit", result.returncode, flush=True)
    return name, result.returncode


with ThreadPoolExecutor(max_workers=2) as queue:
    results = list(queue.map(replay, cases))
assert all(code == 0 for _, code in results), results
print("All three merged-tree replays passed.", flush=True)
