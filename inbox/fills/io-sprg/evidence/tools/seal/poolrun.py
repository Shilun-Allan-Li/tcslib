# poolrun.py (bb1-sim, Claude lead, 2026-11-17): runner_full.py with a pool, after the Lean-parallelism ruling
# (workflow.md §4.1 on main, PR #353; evidence/logs/parallelism-ruling.txt). Same record format (results.jsonl,
# mods/<module>.log, the G26-N1 error count, `lean -DmaxErrors=0 <module>.lean` with no `-o`, so nothing is written
# to <tree>). Changes: up to $POOL probes of this run at once (threads), and every Lean process first takes one of
# $POOL host-wide slot locks /home/user/fill/locks/slot<i> (a counting semaphore shared by every concurrent run, so
# the host never runs more than $POOL Lean processes), and waits while MemAvailable is below $MEM_FLOOR_GB (default
# 4). A sampler thread appends `<utc> MemAvailable-kB <n>` to <logdir>/memory.log every 2 s; results.jsonl records
# each probe's maxrss_kb and its slot. Probes are distinct files, each with its own log.
r"""poolrun.py <worktree> <order> <tree> <logdir>"""
import sys, os, re, json, time, hashlib, subprocess, datetime, glob, threading, fcntl
from concurrent.futures import ThreadPoolExecutor
wt, order, tree, logdir = sys.argv[1:5]
POOL = int(os.environ.get('POOL', '3')); FLOOR = float(os.environ.get('MEM_FLOOR_GB', '4')) * 2**20
os.makedirs(os.path.join(logdir, 'mods'), exist_ok=True)
env = dict(os.environ)
env['PATH'] = os.path.expanduser('~/.elan/bin') + ':' + env['PATH']
env['LEAN_PATH'] = ':'.join([tree] + [d for d in sorted(glob.glob(os.environ.get('LAKE_PACKAGES', '/home/user/fill/tcslib/.lake/packages') + '/*/.lake/build/lib/lean')) if os.path.isdir(d)])
mods = [l.strip() for l in open(order) if l.strip()]
sha = lambda p: hashlib.sha256(open(p, 'rb').read()).hexdigest() if os.path.exists(p) else None
now = lambda: datetime.datetime.now(datetime.timezone.utc).isoformat(timespec='seconds')
memavail = lambda: int(next(l.split()[1] for l in open('/proc/meminfo') if l.startswith('MemAvailable')))
res = open(os.path.join(logdir, 'results.jsonl'), 'a'); wlock = threading.Lock(); done = threading.Event()
def sampler():
    with open(os.path.join(logdir, 'memory.log'), 'a') as f:
        while not done.is_set():
            f.write(f'{now()} MemAvailable-kB {memavail()}\n'); f.flush(); time.sleep(2)
def acquire():
    while True:
        if memavail() >= FLOOR:
            for i in range(POOL):
                fd = os.open(f'/home/user/fill/locks/slot{i}', os.O_CREAT | os.O_RDWR)
                try:
                    fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB); return i, fd
                except BlockingIOError:
                    os.close(fd)
        time.sleep(1)
def run(m):
    lp = os.path.join(logdir, 'mods', m.replace('/', '_') + '.log')
    slot, fd = acquire()
    try:
        t0 = time.time(); s0 = now()
        with open(lp, 'wb') as out:
            p = subprocess.Popen(['nice', '-n', '10', 'lean', '-DmaxErrors=0', m + '.lean'], cwd=wt, env=env,
                                 stdout=out, stderr=subprocess.STDOUT)
            _, status, ru = os.wait4(p.pid, 0)
    finally:
        fcntl.flock(fd, fcntl.LOCK_UN); os.close(fd)
    rc = os.waitstatus_to_exitcode(status)
    txt = open(lp, encoding='utf-8', errors='replace').read()
    rec = dict(module=m, rc=rc, errors=len(re.findall(r'^\S+\.lean:\d+:\d+: error[:(]', txt, re.M)), error_substr=txt.count('error'),
               sorry=txt.count("declaration uses 'sorry'"), warnings=len(re.findall(r'warning:', txt)), start=s0, end=now(),
               seconds=round(time.time() - t0, 2), maxrss_kb=ru.ru_maxrss, source_sha256=sha(os.path.join(wt, m + '.lean')),
               object_sha256=None, log_sha256=sha(lp), maxErrors=0, slot=slot, pool=POOL)
    with wlock:
        res.write(json.dumps(rec) + '\n'); res.flush()
threading.Thread(target=sampler, daemon=True).start()
with ThreadPoolExecutor(max_workers=POOL) as ex:
    list(ex.map(run, mods))
done.set()
res.write(json.dumps(dict(done=now(), order=order, pool=POOL)) + '\n')
