#!/usr/bin/env python3
"""Run scripts/lean_check_tree.sh on one module under the host-wide Lean lock.

Usage: python3 -I check.py <worktree> <module> <logfile>
Environment: TCSLIB_OLEANS selects the olean tree (default: the worktree's own).
Appends a summary line to <logfile>.summary: module, rc, error count, sorry warnings,
start, end, max RSS (KiB).
"""
import fcntl, os, re, resource, subprocess, sys, time
wt, mod, log = sys.argv[1], sys.argv[2], sys.argv[3]
LOCK = '/home/user/gsw6a/.lean.lock'
env = dict(os.environ)
env['PATH'] = os.path.expanduser('~/.elan/bin') + ':' + env.get('PATH', '')
os.makedirs(os.path.dirname(os.path.abspath(log)), exist_ok=True)
with open(LOCK, 'w') as lk:
    fcntl.flock(lk, fcntl.LOCK_EX)
    t0 = time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())
    p = subprocess.run(['bash', 'scripts/lean_check_tree.sh', mod], cwd=wt, env=env,
                       stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    t1 = time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())
    fcntl.flock(lk, fcntl.LOCK_UN)
rss = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss
out = p.stdout
errs = len(re.findall(r'^\S+\.lean:\d+:\d+: error[:(]', out, re.M))
sorries = len(re.findall(r"declaration uses 'sorry'", out))
with open(log, 'a') as f:
    f.write(f'=== {mod} start {t0}\n{out}=== {mod} end {t1} rc={p.returncode} '
            f'errors={errs} sorry={sorries} maxrss_kib={rss}\n')
line = f'{mod}\trc={p.returncode}\terrors={errs}\tsorry={sorries}\t{t0}\t{t1}\tmaxrss_kib={rss}'
with open(log + '.summary', 'a') as f:
    f.write(line + '\n')
print(line)
if p.returncode != 0 or errs:
    print(out[-4000:])
sys.exit(p.returncode)
