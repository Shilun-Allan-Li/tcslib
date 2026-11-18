# io-sprg Mac adaptation (Codex preflight agent, 2026-11-18).
# Source: exchange 2467bc3befdad8472b1f359337bf3a203e3651e1,
# inbox/fills/bb1-sim/evidence/tools/seal/runner_full.py.
# Host paths changed: /home/user/fill/tcslib/.lean.lock (flock $LEAN_LOCK)
# -> /private/tmp/io-sprg-tools/lean-slot.sh (pinned host-wide Mac wrapper);
# /home/user/fill/tcslib/.lake/packages -> <worktree>/.lake/packages
# (LAKE_PACKAGES override retained). LEAN_SLOT_TAG is set to io-sprg.
# Mac ru_maxrss bytes are divided by 1024 to preserve the maxrss_kb record unit.
# Lean arguments, no-output mode, error counting, and queue semantics are unchanged.
# bb1-sim (lead): copied unchanged from bb1-sim-statements (exchange a3cb45f6, evidence/tools/seal/).
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
env['LEAN_SLOT_TAG'] = 'io-sprg'
env['LEAN_PATH'] = ':'.join([tree] + [d for d in sorted(glob.glob(os.environ.get('LAKE_PACKAGES', os.path.join(wt, '.lake', 'packages')) + '/*/.lake/build/lib/lean')) if os.path.isdir(d)])
mods = [l.strip() for l in open(order) if l.strip()]
sha = lambda p: hashlib.sha256(open(p, 'rb').read()).hexdigest() if os.path.exists(p) else None
now = lambda: datetime.datetime.now(datetime.timezone.utc).isoformat(timespec='seconds')
res = open(os.path.join(logdir, 'results.jsonl'), 'a')
for m in mods:
    lp = os.path.join(logdir, 'mods', m.replace('/', '_') + '.log')
    t0 = time.time(); s0 = now()
    with open(lp, 'wb') as out:
        p = subprocess.Popen(['/private/tmp/io-sprg-tools/lean-slot.sh', 'nice', '-n', '10', 'lean', '-DmaxErrors=0', m + '.lean'], cwd=wt, env=env,
                             stdout=out, stderr=subprocess.STDOUT)
        with open(os.path.join(logdir, 'current.pid'), 'w') as f: f.write(f'{p.pid} {m}\n')
        _, status, ru = os.wait4(p.pid, 0)
    rc = os.waitstatus_to_exitcode(status)
    txt = open(lp, encoding='utf-8', errors='replace').read()
    rec = dict(module=m, rc=rc, errors=len(re.findall(r'^\S+\.lean:\d+:\d+: error[:(]', txt, re.M)), error_substr=txt.count('error'),
               sorry=txt.count("declaration uses 'sorry'"), warnings=len(re.findall(r'warning:', txt)), start=s0, end=now(),
               seconds=round(time.time() - t0, 2), maxrss_kb=ru.ru_maxrss / 1024 if sys.platform == 'darwin' else ru.ru_maxrss, source_sha256=sha(os.path.join(wt, m + '.lean')),
               object_sha256=None, log_sha256=sha(lp), maxErrors=0)
    res.write(json.dumps(rec) + '\n'); res.flush()
res.write(json.dumps(dict(done=now(), order=order)) + '\n')
