"""Run one command under the host-wide Lean lock, logging start/end and peak child RSS.

usage: python3 -I runlean.py LOG -- CMD...
The lock is flock(2) on /home/user/gsw/.lean.lock, shared by the lead and every sub-agent.
Output goes to LOG (overwritten) and stdout. Exit status is the command's.
"""
import fcntl, resource, subprocess, sys, time
LOCK = "/home/user/gsw/.lean.lock"
log = sys.argv[1]; assert sys.argv[2] == "--"; cmd = sys.argv[3:]
with open(LOCK, "w") as lk:
    t0 = time.time(); fcntl.flock(lk, fcntl.LOCK_EX); waited = time.time() - t0
    start = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    p = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    end = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    rss = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss
with open(log, "w") as f:
    f.write(p.stdout)
    f.write(f"[runlean] cmd={' '.join(cmd)}\n[runlean] lock_wait={waited:.1f}s start={start} end={end} "
            f"exit={p.returncode} max_rss_kib={rss}\n")
sys.stdout.write(p.stdout); print(f"[runlean] start={start} end={end} exit={p.returncode} max_rss_kib={rss}")
sys.exit(p.returncode)
