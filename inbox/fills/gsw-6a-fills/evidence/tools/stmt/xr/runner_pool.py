r"""runner_pool.py (gsw-6a-fills; replaces runner_lock.py of the 6a statement job, whose host-wide lock path no
longer exists): runner_pool.py <worktree> <order> <tree> <logdir> [<parallel>]. Same record format (results.jsonl,
mods/<module>.log, G26-N1 error count `^\S+\.lean:\d+:\d+: error[:(]`); each probe runs
`lean -DmaxErrors=0 <module>.lean` with LEAN_PATH = <tree> plus the lake packages and NO `-o` (nothing is
written to <tree>), each under one slot of the shared Lean pool (../../poollib.py), several at once (threads,
default 3; the pool bounds the real concurrency). Probes are independent (no probe imports another)."""
import sys, os, re, json, time, hashlib, subprocess, datetime, glob, threading
sys.path.insert(0, '/home/user/w6/tools')
import poollib
wt, order, tree, logdir = sys.argv[1:5]
par = int(sys.argv[5]) if len(sys.argv) > 5 else 3
os.makedirs(os.path.join(logdir, 'mods'), exist_ok=True)
env = dict(os.environ)
env['PATH'] = os.path.expanduser('~/.elan/bin') + ':' + env['PATH']
env['LEAN_PATH'] = ':'.join([tree] + [d for d in sorted(glob.glob(os.path.join(wt, '.lake/packages/*/.lake/build/lib/lean'))) if os.path.isdir(d)])
mods = [l.strip() for l in open(order) if l.strip()]
sha = lambda p: hashlib.sha256(open(p, 'rb').read()).hexdigest() if os.path.exists(p) else None
now = lambda: datetime.datetime.now(datetime.timezone.utc).isoformat(timespec='seconds')
res = open(os.path.join(logdir, 'results.jsonl'), 'a'); lk = threading.Lock(); q = list(mods)
def work():
    while True:
        with lk:
            if not q: return
            m = q.pop(0)
        lp = os.path.join(logdir, 'mods', m.replace('/', '_') + '.log')
        t0 = time.time(); s0 = now()
        with open(lp, 'wb') as out:
            rc, rss, sec = poollib.run(f'{os.path.basename(logdir)}:{m}', ['lean', '-DmaxErrors=0', m + '.lean'],
                                       cwd=wt, env=env, stdout=out)
        txt = open(lp, encoding='utf-8', errors='replace').read()
        rec = dict(module=m, rc=rc, errors=len(re.findall(r'^\S+\.lean:\d+:\d+: error[:(]', txt, re.M)),
                   error_substr=txt.count('error'), sorry=txt.count("declaration uses 'sorry'"),
                   warnings=len(re.findall(r'warning:', txt)), start=s0, end=now(), seconds=sec, maxrss_kb=rss,
                   source_sha256=sha(os.path.join(wt, m + '.lean')), object_sha256=None, log_sha256=sha(lp), maxErrors=0)
        with lk: res.write(json.dumps(rec) + '\n'); res.flush()
ts = [threading.Thread(target=work) for _ in range(par)]
for t in ts: t.start()
for t in ts: t.join()
res.write(json.dumps(dict(done=now(), order=order)) + '\n')
