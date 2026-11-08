from pathlib import Path
import datetime
import hashlib
import json
import os
import subprocess
import sys
import time

scratch = Path(os.environ["TCSLIB_SCRATCH"])
records = Path("/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4")
replay = records / "campaign/status/2026-11-08-audit-closures/combined-replay-mjoint1"
work = Path("/private/tmp/ab34-joint-axioms")
receipt = json.loads((replay / "receipt.json").read_text())
assert receipt["result"] == "PASS" and receipt["pipeline_exit"] == 0
wt = scratch / "wt-camp"
snapshot = scratch / "oleans-mjoint1"
head = subprocess.check_output(["git", "-C", str(wt), "rev-parse", "HEAD"], text=True).strip()
assert head == receipt["source"]
assert not subprocess.check_output(["git", "-C", str(wt), "status", "--porcelain", "--untracked-files=no"], text=True).strip()

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def object_map():
    return {p.relative_to(snapshot).as_posix(): digest(p) for p in sorted(snapshot.rglob("*.olean"))}

expected_objects = json.loads((replay / "snapshot-objects.json").read_text())["output_MJOINT1"]
assert len(expected_objects) == 895 and object_map() == expected_objects
probe = work / "JointAxioms.lean"
probe_sha = digest(probe)
started = datetime.datetime.now(datetime.timezone.utc).isoformat()
start_clock = time.monotonic()
log = work / "JointAxioms.out"
assert not log.exists(), "preserve an earlier attempt instead of overwriting it"
command = ["bash", str(records / "devtools/seyoon/leanelab.sh"), str(wt), str(snapshot), str(probe)]
with log.open("wb") as stream:
    run = subprocess.run(command, stdout=stream, stderr=subprocess.STDOUT)
run_receipt = dict(
    started_utc=started, ended_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    elapsed_seconds=time.monotonic() - start_clock, exit=run.returncode,
    command=command, source=head, replay_receipt_sha256=digest(replay / "receipt.json"),
    snapshot_map_sha256=digest(replay / "snapshot-objects.json"),
    probe_sha256=probe_sha, probe_unchanged=digest(probe) == probe_sha,
    all895_object_hashes_unchanged=object_map() == expected_objects,
    output_sha256=digest(log), output_bytes=log.stat().st_size,
    scope="Fresh all-constant AX metadata only in the20 selected imported owners; no type/proof value rendering, no global admission-free or opacity claim.",
)
(work / "run.json").write_text(json.dumps(run_receipt, indent=2) + "\n")
assert run_receipt["probe_unchanged"] and run_receipt["all895_object_hashes_unchanged"]
print(json.dumps(run_receipt, indent=2))
sys.exit(run.returncode)
