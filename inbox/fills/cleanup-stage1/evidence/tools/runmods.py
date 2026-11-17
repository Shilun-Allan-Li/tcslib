#!/usr/bin/env python3
"""Check TCSlib modules one at a time through scripts/lean_check_tree.sh.

cleanup-stage1 (lead tool, written for this job).  For every module of an order file:
  * takes the host-wide Lean lock (fcntl.flock on LOCK, default <clone>/.lean.lock),
    released between modules, so that all agents run one Lean process at a time;
  * runs `bash scripts/lean_check_tree.sh <module>` from the clone root with TCSLIB_OLEANS=<tree>;
  * writes the raw output to <logdir>/<module with / replaced by __>.log;
  * records start/end (UTC), wall seconds, max RSS (wait4 rusage, KiB), rc, errors in both
    forms (^\\S+\\.lean:\\d+:\\d+: error[:(]), lines containing "error:" or "error(",
    `declaration uses 'sorry'` warnings, and the SHA-256 of the checked file and of
    `git show HEAD:<file>` (the binding to HEAD) in <logdir>/results.jsonl;
  * stops at the first failure unless --keep-going;
  * sleeps --yield-secs (default 3) after releasing the lock, so that waiting agents get it.
Usage: python3 -I runmods.py --clone C --tree T --logdir D --order F [--from N] [--to N]
"""
import argparse, datetime, fcntl, hashlib, json, os, re, subprocess, sys, time

ERR = re.compile(r'^\S+\.lean:\d+:\d+: error[:(]', re.M)
ap = argparse.ArgumentParser()
ap.add_argument('--clone', required=True)
ap.add_argument('--tree', required=True)
ap.add_argument('--logdir', required=True)
ap.add_argument('--order', required=True)
ap.add_argument('--lock', default=None)
ap.add_argument('--from', dest='frm', type=int, default=1)
ap.add_argument('--to', type=int, default=10 ** 9)
ap.add_argument('--keep-going', action='store_true')
ap.add_argument('--yield-secs', type=float, default=3.0)
a = ap.parse_args()
lock = a.lock or os.path.join(a.clone, '.lean.lock')
os.makedirs(a.logdir, exist_ok=True)
mods = [l.strip() for l in open(a.order) if l.strip() and not l.startswith('#')]
env = dict(os.environ, TCSLIB_OLEANS=a.tree)
res = open(os.path.join(a.logdir, 'results.jsonl'), 'a')
now = lambda: datetime.datetime.now(datetime.timezone.utc).strftime('%Y-%m-%dT%H:%M:%SZ')
bad = 0
for i, m in enumerate(mods, 1):
    if i < a.frm or i > a.to:
        continue
    path = m + '.lean'
    src = open(os.path.join(a.clone, path), 'rb').read()
    try:
        head = subprocess.run(['git', '-C', a.clone, 'show', 'HEAD:' + path],
                              capture_output=True, check=True).stdout
        hh = hashlib.sha256(head).hexdigest()
    except subprocess.CalledProcessError:
        hh = 'NOT-IN-HEAD'
    log = os.path.join(a.logdir, m.replace('/', '__') + '.log')
    with open(lock, 'w') as lf:
        fcntl.flock(lf, fcntl.LOCK_EX)
        t0, s0 = time.time(), now()
        with open(log, 'wb') as out:
            p = subprocess.Popen(['bash', 'scripts/lean_check_tree.sh', m], cwd=a.clone,
                                 env=env, stdout=out, stderr=subprocess.STDOUT)
            _, status, ru = os.wait4(p.pid, 0)
        rc = os.waitstatus_to_exitcode(status)
        t1, s1 = time.time(), now()
        fcntl.flock(lf, fcntl.LOCK_UN)
    time.sleep(a.yield_secs)  # let other agents waiting on the lock take it
    text = open(log, encoding='utf-8', errors='replace').read()
    rec = dict(i=i, module=m, rc=rc, start=s0, end=s1, secs=round(t1 - t0, 1),
               maxrss_kib=ru.ru_maxrss, errors=len(ERR.findall(text)),
               error_lines=sum(1 for l in text.splitlines() if 'error:' in l or 'error(' in l),
               sorry=text.count("declaration uses 'sorry'"),
               src_sha256=hashlib.sha256(src).hexdigest(), head_sha256=hh,
               bound=hashlib.sha256(src).hexdigest() == hh)
    res.write(json.dumps(rec) + '\n'); res.flush()
    print(f"{i}\t{m}\trc={rc}\terr={rec['errors']}\tsorry={rec['sorry']}\t{rec['secs']}s\t"
          f"{ru.ru_maxrss // 1024}MiB", flush=True)
    if rc != 0 or rec['errors'] or rec['error_lines']:
        bad += 1
        if not a.keep_going:
            print('STOP: failure at', i, m, flush=True)
            sys.exit(1)
print('DONE bad=%d' % bad, flush=True)
sys.exit(1 if bad else 0)
