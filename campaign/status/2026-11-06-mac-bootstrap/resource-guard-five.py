"""Keep this task within the user's global cap of five; signal only owned jobs."""

from pathlib import Path
import json
import os
import signal
import subprocess
import time


scratch = Path(os.environ["TCSLIB_SCRATCH"])
stopped: set[int] = set()
log = scratch / "setup/resource-five-events.jsonl"
while not (scratch / "setup/resource-five.stop").exists():
    ours, external = [], []
    raw = subprocess.check_output(["ps", "-A", "-o", "pid=,stat=,command="], text=True)
    for line in raw.splitlines():
        p = line.strip().split(maxsplit=2)
        if len(p) != 3 or "Z" in p[1]:
            continue
        pid, state, cmd = int(p[0]), p[1], p[2]
        if not (cmd.split()[0].endswith("/lean") or cmd.startswith("lean ")):
            continue
        owned = any(str(scratch / n) in cmd for n in (
            "oleans-msg1/", "oleans-mnb1/", "oleans-mepad1/", "gate-probes/"))
        if owned:
            ours.append((pid, state))
        elif "T" not in state:
            external.append(pid)
    budget = max(0, 5 - len(external))
    running = sorted(pid for pid, state in ours if "T" not in state)
    for pid in running[budget:]:
        try:
            os.kill(pid, signal.SIGSTOP)
        except ProcessLookupError:
            continue
        stopped.add(pid)
        with log.open("a") as output:
            output.write(json.dumps({"event": "suspend-own", "pid": pid,
                                     "external_active": len(external)}) + "\n")
    free = max(0, budget - min(len(running), budget))
    for pid, state in sorted(ours):
        if free and pid in stopped and "T" in state:
            try:
                os.kill(pid, signal.SIGCONT)
            except ProcessLookupError:
                continue
            stopped.discard(pid)
            free -= 1
            with log.open("a") as output:
                output.write(json.dumps({"event": "resume-own", "pid": pid,
                                         "external_active": len(external)}) + "\n")
    time.sleep(1)
print("Five-process resource guard stopped.")
