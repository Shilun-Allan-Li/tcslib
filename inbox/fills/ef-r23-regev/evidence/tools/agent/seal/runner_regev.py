# runner_regev.py -- ADAPTED by tools-agent (sub-agent of fill ef-r23-regev, 2026-11-18) from
#   /home/user/ef-r23/tools/bb1m-tools/seal/runner_full.py (fill bb1-machine's adaptation of the sc-garble
#   review runner_full.py). Adaptations, nothing else changed in the record format:
#   (1) lake packages from $LAKE_PACKAGES, default /home/user/ef-r23/repo/.lake/packages (this fill's clone);
#   (2) the single-host `flock $LEAN_LOCK` wrapper is REMOVED (cloud worker; the lead controls concurrency);
#   (3) at most N Lean processes at once, N = $RULE10_JOBS (default 2, must be >= 1); results.jsonl lines are
#       written in completion order (each record names its module, so ctlcheck2.py/sealsum.py are unaffected);
#       current.pid lists every running pid;
#   (4) `elan` toolchain from ~/.elan/bin as before; the probe's lean is whatever `lean` that PATH resolves
#       (the repo's lean-toolchain pins v4.25.0 through elan).
#   (5) DRY=1 prints the LEAN_PATH and the exact commands without running Lean (no records written).
r"""runner_regev.py <worktree> <order> <tree> <logdir> (sc-garble review runner_full.py lineage): runner.py's record format
(results.jsonl, mods/<module>.log, G26-N1 error count `^\S+\.lean:\d+:\d+: error[:(]`), each probe runs
`lean -DmaxErrors=0 <module>.lean` directly (cwd <worktree>), with LEAN_PATH = <tree> plus every
$LAKE_PACKAGES/*/.lake/build/lib/lean, and NO `-o`: nothing is written to <tree>. Does not stop on failure."""
import sys, os, re, json, time, hashlib, subprocess, datetime, glob
wt, order, tree, logdir = sys.argv[1:5]
JOBS = int(os.environ.get('RULE10_JOBS', '2'))
assert JOBS >= 1, 'RULE10_JOBS must be >= 1'
env = dict(os.environ)
env['PATH'] = os.path.expanduser('~/.elan/bin') + ':' + env['PATH']
pk = os.environ.get('LAKE_PACKAGES', '/home/user/ef-r23/repo/.lake/packages')
env['LEAN_PATH'] = ':'.join([tree] + [d for d in sorted(glob.glob(pk + '/*/.lake/build/lib/lean')) if os.path.isdir(d)])
mods = [l.strip() for l in open(order) if l.strip()]
if os.environ.get('DRY') == '1':
    print('LEAN_PATH=' + env['LEAN_PATH'])
    for m in mods: print(f'(cd {wt} && nice -n 10 lean -DmaxErrors=0 {m}.lean)')
    sys.exit(0)
os.makedirs(os.path.join(logdir, 'mods'), exist_ok=True)
sha = lambda p: hashlib.sha256(open(p, 'rb').read()).hexdigest() if os.path.exists(p) else None
now = lambda: datetime.datetime.now(datetime.timezone.utc).isoformat(timespec='seconds')
res = open(os.path.join(logdir, 'results.jsonl'), 'a')
running = {}  # pid -> (module, logpath, t0, s0, filehandle, Popen); the Popen object is kept alive so that
# subprocess's own cleanup (Popen.__del__ -> _cleanup) never reaps a child before os.wait4 sees it
def write_pids():
    with open(os.path.join(logdir, 'current.pid'), 'w') as f:
        for pid, v in running.items(): f.write(f'{pid} {v[0]}\n')
def reap():
    pid, status, ru = os.wait4(-1, 0)
    if pid not in running: return
    m, lp, t0, s0, fh, proc = running.pop(pid); fh.close(); proc.returncode = os.waitstatus_to_exitcode(status); write_pids()
    rc = os.waitstatus_to_exitcode(status)
    txt = open(lp, encoding='utf-8', errors='replace').read()
    rec = dict(module=m, rc=rc, errors=len(re.findall(r'^\S+\.lean:\d+:\d+: error[:(]', txt, re.M)), error_substr=txt.count('error'),
               sorry=txt.count("declaration uses 'sorry'"), warnings=len(re.findall(r'warning:', txt)), start=s0, end=now(),
               seconds=round(time.time() - t0, 2), maxrss_kb=ru.ru_maxrss, source_sha256=sha(os.path.join(wt, m + '.lean')),
               object_sha256=None, log_sha256=sha(lp), maxErrors=0, jobs=JOBS)
    res.write(json.dumps(rec) + '\n'); res.flush()
for m in mods:
    while len(running) >= JOBS: reap()
    lp = os.path.join(logdir, 'mods', m.replace('/', '_') + '.log')
    out = open(lp, 'wb')
    p = subprocess.Popen(['nice', '-n', '10', 'lean', '-DmaxErrors=0', m + '.lean'], cwd=wt, env=env,
                         stdout=out, stderr=subprocess.STDOUT)
    running[p.pid] = (m, lp, time.time(), now(), out, p); write_pids()
while running: reap()
res.write(json.dumps(dict(done=now(), order=order)) + '\n')
