"""runner.py <worktree> <order> <tree> <logdir> [start-module]
Checks modules in order, one Lean process at a time, through scripts/lean_check_tree.sh with
TCSLIB_OLEANS=<tree>. Per module: full log <logdir>/mods/<module with / -> _>.log and a JSON line
in <logdir>/results.jsonl (rc, error/sorry/warning counts, start/end UTC, seconds, maxrss_kb of
the checker process tree, source and object SHA-256). Stops at the first failure (like ladder.sh)."""
import sys, os, json, time, hashlib, subprocess, datetime, re
wt, order, tree, logdir = sys.argv[1:5]
start = sys.argv[5] if len(sys.argv) > 5 else None
os.makedirs(os.path.join(logdir, 'mods'), exist_ok=True)
env = dict(os.environ)
env['PATH'] = os.path.expanduser('~/.elan/bin') + ':' + env['PATH']
env['TCSLIB_OLEANS'] = tree
mods = [l.strip() for l in open(order) if l.strip()]
on = start is None
sha = lambda p: hashlib.sha256(open(p, 'rb').read()).hexdigest() if os.path.exists(p) else None
now = lambda: datetime.datetime.now(datetime.timezone.utc).isoformat(timespec='seconds')
res = open(os.path.join(logdir, 'results.jsonl'), 'a')
for m in mods:
    if not on:
        if m == start: on = True
        else: continue
    lp = os.path.join(logdir, 'mods', m.replace('/', '_') + '.log')
    t0 = time.time(); s0 = now()
    with open(lp, 'wb') as out:
        p = subprocess.Popen(['nice', '-n', '10', 'bash', 'scripts/lean_check_tree.sh', m], cwd=wt, env=env,
                             stdout=out, stderr=subprocess.STDOUT)
        with open(os.path.join(logdir, 'current.pid'), 'w') as f: f.write(f'{p.pid} {m}\n')
        _, status, ru = os.wait4(p.pid, 0)
    rc = os.waitstatus_to_exitcode(status)
    txt = open(lp, encoding='utf-8', errors='replace').read()
    rec = dict(module=m, rc=rc, errors=len(re.findall(r'error:', txt)), sorry=txt.count("declaration uses 'sorry'"),
               warnings=len(re.findall(r'warning:', txt)), start=s0, end=now(), seconds=round(time.time() - t0, 2),
               maxrss_kb=ru.ru_maxrss, source_sha256=sha(os.path.join(wt, m + '.lean')),
               object_sha256=sha(os.path.join(tree, m + '.olean')), log_sha256=sha(lp))
    res.write(json.dumps(rec) + '\n'); res.flush()
    if rc != 0 and not os.environ.get('NOSTOP'):
        res.write(json.dumps(dict(stopped_at=m, utc=now())) + '\n'); sys.exit(1)
res.write(json.dumps(dict(done=now(), order=order)) + '\n')
