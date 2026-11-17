# dw10-seal-inventory (Claude lead, 2026-11-17): ADAPTED from the bb1-sim-statements delivery. Changes: (1) host paths:
#   $LAKE_PACKAGES defaults to /home/user/dw10/lead/.lake/packages and $LEAN_LOCK to /home/user/dw10/lead/.lean.lock (the
#   lead's packages and the host's one-Lean lock, taken per probe); (2) resume: a probe module that already has a record in
#   <logdir>/results.jsonl is skipped (background jobs on this host stop after 2 h; a probe interrupted mid-run has no record
#   and is re-run from scratch, its log overwritten). Nothing else changed.
# bb1-sim-statements (lead): copied unchanged from the bb1-machine delivery (host paths already this job's).
# ADAPTED (fill bb1-machine, Claude lead, 2026-11-16): (1) the lake packages are read from
#   $LAKE_PACKAGES (default /home/user/fill/tcslib/.lake/packages, the lead clone's), not
#   /home/user/tcslib/.lake/packages; (2) every probe runs under `flock $LEAN_LOCK` (default
#   /home/user/fill/tcslib/.lean.lock), taken per probe. Nothing else changed.
r"""runner_full.py <worktree> <order> <tree> <logdir> (sc-garble review): runner.py's record format (results.jsonl, mods/<module>.log,
G26-N1 error count `^\S+\.lean:\d+:\d+: error[:(]`), but each probe runs `lean -DmaxErrors=0 <module>.lean` directly, with
the LEAN_PATH of probe.sh (<tree> plus the lake packages) and NO `-o`: nothing is written to <tree> (canonizer C-F02: full-file
seals are not cut at Lean's default 100 errors). One Lean process at a time; does not stop on failure."""
import sys, os, re, json, time, hashlib, subprocess, datetime, glob
wt, order, tree, logdir = sys.argv[1:5]
os.makedirs(os.path.join(logdir, 'mods'), exist_ok=True)
env = dict(os.environ)
env['PATH'] = os.path.expanduser('~/.elan/bin') + ':' + env['PATH']
env['LEAN_PATH'] = ':'.join([tree] + [d for d in sorted(glob.glob(os.environ.get('LAKE_PACKAGES', '/home/user/dw10/lead/.lake/packages') + '/*/.lake/build/lib/lean')) if os.path.isdir(d)])
mods = [l.strip() for l in open(order) if l.strip()]
sha = lambda p: hashlib.sha256(open(p, 'rb').read()).hexdigest() if os.path.exists(p) else None
now = lambda: datetime.datetime.now(datetime.timezone.utc).isoformat(timespec='seconds')
done_mods = set()
for _f in glob.glob(os.path.join(logdir, 'results*.jsonl')):
    for _l in open(_f):
        _x = json.loads(_l)
        if 'module' in _x: done_mods.add(_x['module'])
_tag = os.environ.get('RUN_TAG')
res = open(os.path.join(logdir, f'results-{_tag}.jsonl' if _tag else 'results.jsonl'), 'a')
MEM_MIN = float(os.environ.get('MEM_MIN_GB', '4.5')) * 1024 ** 3
def _avail():
    for _l in open('/proc/meminfo'):
        if _l.startswith('MemAvailable:'): return int(_l.split()[1]) * 1024
    return 0
for m in mods:
    if m in done_mods: continue
    _cd = os.path.join(logdir, 'claims'); os.makedirs(_cd, exist_ok=True); _cp = os.path.join(_cd, m.replace('/', '_') + '.claim')
    try:
        _fd = os.open(_cp, os.O_CREAT | os.O_EXCL | os.O_WRONLY); os.write(_fd, str(os.getpid()).encode()); os.close(_fd)
    except FileExistsError:
        try: _pid = int(open(_cp).read().strip() or 0)
        except Exception: _pid = 0
        _alive = False
        try: os.kill(_pid, 0); _alive = _pid > 0
        except Exception: _alive = False
        _rec = any(json.loads(_l).get('module') == m for _f in glob.glob(os.path.join(logdir, 'results*.jsonl')) for _l in open(_f))
        if _alive or _rec: continue
        open(_cp, 'w').write(str(os.getpid()))
    _w = 0
    while _avail() < MEM_MIN:
        if _w % 12 == 0: print(f'memwait {m} avail={_avail()}', flush=True)
        _w += 1; time.sleep(5)
    lp = os.path.join(logdir, 'mods', m.replace('/', '_') + '.log')
    t0 = time.time(); s0 = now()
    with open(lp, 'wb') as out:
        p = subprocess.Popen(['flock', os.environ.get('LEAN_LOCK', '/home/user/dw10/lead/.lean.lock'), 'nice', '-n', '10', 'lean', '-DmaxErrors=0', m + '.lean'], cwd=wt, env=env,
                             stdout=out, stderr=subprocess.STDOUT)
        with open(os.path.join(logdir, 'current.pid'), 'w') as f: f.write(f'{p.pid} {m}\n')
        _, status, ru = os.wait4(p.pid, 0)
    rc = os.waitstatus_to_exitcode(status)
    txt = open(lp, encoding='utf-8', errors='replace').read()
    rec = dict(module=m, rc=rc, errors=len(re.findall(r'^\S+\.lean:\d+:\d+: error[:(]', txt, re.M)), error_substr=txt.count('error'),
               sorry=txt.count("declaration uses 'sorry'"), warnings=len(re.findall(r'warning:', txt)), start=s0, end=now(),
               seconds=round(time.time() - t0, 2), maxrss_kb=ru.ru_maxrss, source_sha256=sha(os.path.join(wt, m + '.lean')),
               object_sha256=None, log_sha256=sha(lp), maxErrors=0)
    res.write(json.dumps(rec) + '\n'); res.flush()
res.write(json.dumps(dict(done=now(), order=order)) + '\n')
