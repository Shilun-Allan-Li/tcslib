r"""runner_pool.py <worktree> <order> <tree> <logdir> [jobs] (gsw-6b-statements sub-agent `seal`, new; a copy of
runner_lock.py / runner_full.py with these changes):
  * the host-wide flock (/home/user/gsw6a/.lean.lock) is replaced by one slot of the shared Lean pool
    (/home/user/ev/tools/lead/poollib.py; pool size 3 shared by all agents, MemAvailable floor);
  * LEAN_PATH = <tree> plus <worktree>/.lake/packages/*/.lake/build/lib/lean (as scripts/lean_check_tree.sh forms it;
    the 6a runner_full.py read /home/user/tcslib/.lake/packages);
  * up to [jobs] (default 1) probes are submitted at once (each still waits for its own pool slot); the records are
    written in completion order, one line each, under a lock;
  * the max RSS per probe comes from poollib.run (wait4 of the one child).
Unchanged: record format (results.jsonl, mods/<module>.log, G26-N1 error count `^\S+\.lean:\d+:\d+: error[:(]`), each
probe runs `nice -n 10 lean -DmaxErrors=0 <module>.lean` from <worktree> with NO `-o` (nothing is written to <tree>);
does not stop on failure. A module listed twice is refused (never two processes on one file)."""
import sys, os, re, json, time, hashlib, datetime, glob, threading
sys.path.insert(0, '/home/user/ev/tools/lead')
import poollib
wt, order, tree, logdir = sys.argv[1:5]
jobs = int(sys.argv[5]) if len(sys.argv) > 5 else 1
os.makedirs(os.path.join(logdir, 'mods'), exist_ok=True)
env = dict(os.environ)
env['PATH'] = os.path.expanduser('~/.elan/bin') + ':' + env['PATH']
env['LEAN_PATH'] = ':'.join([tree] + [d for d in sorted(glob.glob(os.path.join(wt, '.lake/packages/*/.lake/build/lib/lean'))) if os.path.isdir(d)])
mods = [l.strip() for l in open(order) if l.strip()]
assert len(mods) == len(set(mods)), 'duplicate module in order file'
sha = lambda p: hashlib.sha256(open(p, 'rb').read()).hexdigest() if os.path.exists(p) else None
now = lambda: datetime.datetime.now(datetime.timezone.utc).isoformat(timespec='seconds')
res = open(os.path.join(logdir, 'results.jsonl'), 'a')
lock = threading.Lock()
def one(m):
    lp = os.path.join(logdir, 'mods', m.replace('/', '_') + '.log')
    s0 = now(); src0 = sha(os.path.join(wt, m + '.lean'))
    with open(lp, 'wb') as out:
        rc, rss, sec = poollib.run(f'seal:{os.path.basename(logdir)}:{os.path.basename(m)}',
                                   ['nice', '-n', '10', 'lean', '-DmaxErrors=0', m + '.lean'], cwd=wt, env=env, stdout=out)
    txt = open(lp, encoding='utf-8', errors='replace').read()
    rec = dict(module=m, rc=rc, errors=len(re.findall(r'^\S+\.lean:\d+:\d+: error[:(]', txt, re.M)), error_substr=txt.count('error'),
               sorry=txt.count("declaration uses 'sorry'"), warnings=len(re.findall(r'warning:', txt)), start=s0, end=now(),
               seconds=sec, maxrss_kb=rss, source_sha256=src0, source_sha256_end=sha(os.path.join(wt, m + '.lean')),
               object_sha256=None, log_sha256=sha(lp), maxErrors=0)
    with lock:
        res.write(json.dumps(rec) + '\n'); res.flush()
        print(f"{m}\trc={rc}\terrors={rec['errors']}\tseconds={sec}\tmaxrss_kb={rss}", flush=True)
pending = list(mods); running = []
while pending or running:
    running = [t for t in running if t.is_alive()]
    while pending and len(running) < jobs:
        t = threading.Thread(target=one, args=(pending.pop(0),)); t.start(); running.append(t)
    time.sleep(0.5)
res.write(json.dumps(dict(done=now(), order=order)) + '\n')
