#!/usr/bin/env python3
"""Run scripts/lean_check_tree.sh on one module of /workspace/prfmac; log start/end (UTC), wall
time and the maximum RSS of the children (the Lean process)."""
import sys, subprocess, resource, datetime
mod = sys.argv[1]
t0 = datetime.datetime.now(datetime.timezone.utc)
print(f"START {mod} {t0.isoformat(timespec='seconds')}", flush=True)
p = subprocess.run(["bash", "scripts/lean_check_tree.sh", mod], cwd="/workspace/prfmac")
t1 = datetime.datetime.now(datetime.timezone.utc)
rss = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss
print(f"END {mod} {t1.isoformat(timespec='seconds')} exit={p.returncode} "
      f"wall={(t1-t0).total_seconds():.1f}s maxrss={rss//1024}MiB", flush=True)
sys.exit(p.returncode)
