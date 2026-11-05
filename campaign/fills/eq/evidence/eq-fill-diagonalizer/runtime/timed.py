#!/usr/bin/env python3
"""Run a command; print its start/end time (UTC), wall time and the maximum resident set size
of its process tree's largest descendant (getrusage RUSAGE_CHILDREN ru_maxrss, KiB on Linux).
Stand-in for `/usr/bin/time -v`, which this host lacks."""
import resource, subprocess, sys, time, datetime
t0 = time.time()
print(f"TIMED start {datetime.datetime.now(datetime.timezone.utc).replace(tzinfo=None).isoformat()}Z cmd={' '.join(sys.argv[1:])}", flush=True)
p = subprocess.run(sys.argv[1:])
t1 = time.time()
ru = resource.getrusage(resource.RUSAGE_CHILDREN)
print(f"TIMED end {datetime.datetime.now(datetime.timezone.utc).replace(tzinfo=None).isoformat()}Z exit={p.returncode} wall_s={t1-t0:.1f} "
      f"user_s={ru.ru_utime:.1f} sys_s={ru.ru_stime:.1f} maxrss_kib={ru.ru_maxrss}", flush=True)
sys.exit(p.returncode)
