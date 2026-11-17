# boot_driver.py (dw10-seal-inventory, Claude lead, 2026-11-17): NEW. Runs scripts/lean_check_tree.sh on each
# module of an order list, one at a time, each under `flock <LEAN_LOCK>` (the host's one-Lean lock, released between
# modules), and records per module: start, end, seconds, rc, max RSS (wait4 rusage; /usr/bin/time is not installed on
# this host), errors in both forms (^\S+\.lean:\d+:\d+: error[:(]  and the substring 'error'), sorry warnings, the
# source SHA-256 (worktree bytes) and the produced .olean SHA-256. Logs: <logdir>/mods/<module>.log, <logdir>/results.jsonl.
# Usage: python3 -I boot_driver.py <worktree> <order> <olean-tree> <logdir> [--stop-on-fail]
import sys, os, re, json, time, hashlib, subprocess, datetime
wt, order, tree, logdir = sys.argv[1:5]; stop = '--stop-on-fail' in sys.argv
os.makedirs(os.path.join(logdir, 'mods'), exist_ok=True)
env = dict(os.environ); env['PATH'] = os.path.expanduser('~/.elan/bin') + ':' + env['PATH']; env['TCSLIB_OLEANS'] = tree
lock = os.environ.get('LEAN_LOCK', '/home/user/dw10/lead/.lean.lock')
sha = lambda p: hashlib.sha256(open(p, 'rb').read()).hexdigest() if os.path.exists(p) else None
now = lambda: datetime.datetime.now(datetime.timezone.utc).isoformat(timespec='seconds')
done = set()
rp = os.path.join(logdir, 'results.jsonl')
if os.path.exists(rp):
    for l in open(rp):
        x = json.loads(l)
        if x.get('module') and x.get('pass'): done.add(x['module'])
res = open(rp, 'a')
for m in [l.strip() for l in open(order) if l.strip()]:
    if m in done: continue
    lp = os.path.join(logdir, 'mods', m.replace('/', '_') + '.log'); t0 = time.time(); s0 = now()
    with open(lp, 'wb') as out:
        p = subprocess.Popen(['flock', lock, 'bash', 'scripts/lean_check_tree.sh', m], cwd=wt, env=env, stdout=out, stderr=subprocess.STDOUT)
        _, status, ru = os.wait4(p.pid, 0)
    rc = os.waitstatus_to_exitcode(status); txt = open(lp, encoding='utf-8', errors='replace').read()
    rec = dict(module=m, rc=rc, errors=len(re.findall(r'^\S+\.lean:\d+:\d+: error[:(]', txt, re.M)), error_substr=txt.count('error'),
               sorry=txt.count("declaration uses 'sorry'"), start=s0, end=now(), seconds=round(time.time() - t0, 2), maxrss_kb=ru.ru_maxrss,
               source_sha256=sha(os.path.join(wt, m + '.lean')), olean_sha256=sha(os.path.join(tree, m + '.olean')), log_sha256=sha(lp),
               pass_=None)
    rec['pass'] = rc == 0 and rec['errors'] == 0; del rec['pass_']
    res.write(json.dumps(rec) + '\n'); res.flush()
    print(m, rc, rec['errors'], rec['sorry'], rec['seconds'], rec['maxrss_kb'], flush=True)
    if stop and not rec['pass']: sys.exit(1)
res.write(json.dumps(dict(done=now(), order=order)) + '\n')
