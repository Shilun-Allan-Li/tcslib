"""Run scripts/lean_check_tree.sh on one module; log start, end, wall time, max RSS, exit.

Usage: python3 -I timed_check.py <repo-root> <module-path-without-.lean>
Prints the check's own output, then one line:
  TIMING <module> start=<UTC> end=<UTC> wall=<s> maxrss_kib=<KiB> exit=<status>
Max RSS is the largest resident set among the waited-for children (the lean process),
from getrusage(RUSAGE_CHILDREN), as /usr/bin/time -v reports it; /usr/bin/time is absent here.
"""
import datetime, resource, subprocess, sys, time
root, mod = sys.argv[1], sys.argv[2]
utc = lambda: datetime.datetime.now(datetime.timezone.utc).strftime('%Y-%m-%dT%H:%M:%SZ')
s, t0 = utc(), time.monotonic()
p = subprocess.run(['bash', f'{root}/scripts/lean_check_tree.sh', mod], cwd=root,
                   stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
wall = time.monotonic() - t0
rss = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss
sys.stdout.write(p.stdout)
print(f'TIMING {mod} start={s} end={utc()} wall={wall:.1f}s maxrss_kib={rss} exit={p.returncode}', flush=True)
sys.exit(p.returncode)
