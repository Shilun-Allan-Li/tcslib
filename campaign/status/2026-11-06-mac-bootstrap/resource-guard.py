"""Task-local safeguard while another campaign does not share the Lean locks.

Signal only this task's replay/probe Lean processes. Leave them suspended
while any external Lean job is active; resume after 30 seconds without one.
The shared slot locks continue to cap this task at two. No external job is
signaled. Stop via the task's resource-guard.stop file after all checks finish.
"""

from pathlib import Path
import datetime
import json
import os
import signal
import subprocess
import time


scratch = Path(os.environ["TCSLIB_SCRATCH"])
records = Path(__file__).resolve().parents[3]
history = records / "campaign/status/2026-11-06-mac-bootstrap/resource-events.jsonl"
stopped = {row["pid"] for row in json.loads(history.with_name("resource-pause.json").read_text())["suspended"]}
quiet_since = None
(scratch / "setup/resource-guard.pid").write_text(str(os.getpid()) + "\n")
while not (scratch / "setup/resource-guard.stop").exists():
    raw = subprocess.check_output(["ps", "-A", "-o", "pid=,stat=,command="], text=True)
    ours, external = [], []
    for line in raw.splitlines():
        parts = line.strip().split(maxsplit=2)
        if len(parts) != 3:
            continue
        pid, state, command = int(parts[0]), parts[1], parts[2]
        if not (command.split()[0].endswith("/lean") or command.startswith("lean ")):
            continue
        if "Z" in state:
            continue
        owned = any(str(scratch / name) in command for name in (
            "oleans-msg1/", "oleans-mnb1/", "oleans-mepad1/", "gate-probes/"))
        if owned:
            ours.append((pid, state))
        elif "T" not in state:
            external.append(pid)
    if external:
        quiet_since = None
        for pid, state in ours:
            if "T" not in state:
                try:
                    os.kill(pid, signal.SIGSTOP)
                except ProcessLookupError:
                    continue
                stopped.add(pid)
                with history.open("a") as output:
                    output.write(json.dumps({"at_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
                                             "event": "suspend-own", "pid": pid,
                                             "external_active": len(external)}) + "\n")
    else:
        if quiet_since is None:
            quiet_since = time.monotonic()
        if time.monotonic() - quiet_since >= 30:
            for pid, state in ours:
                if pid in stopped and "T" in state:
                    try:
                        os.kill(pid, signal.SIGCONT)
                    except ProcessLookupError:
                        continue
                    stopped.discard(pid)
                    with history.open("a") as output:
                        output.write(json.dumps({"at_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
                                                 "event": "resume-own", "pid": pid,
                                                 "external_active": 0}) + "\n")
    time.sleep(1)
print("Resource guard stopped after task checks.")
