"""[gsw-6b-statements copy of gsw-6a-fills evidence/tools/lead/poollib.py; changes: POOL default /home/user/pool.] poollib.py (gsw-6a-fills, new): the shared Lean pool of workflow.md §4.1 / the addendum's adaptation.
A counting semaphore made of flock slot files <POOL>/slot<i>; the pool size is read from <POOL>/size at
each acquisition (so it can be shrunk under memory pressure); every acquire/release is appended to
<POOL>/pool.log with the slot, the label, MemAvailable and, at release, the exit code and max RSS.
A slot is only taken while MemAvailable >= MEM_FLOOR (2.5 GB), so about 2 GB stays free."""
import fcntl, os, time, datetime, subprocess, resource
POOL = os.environ.get('LEAN_POOL', '/home/user/pool')
MEM_FLOOR = 2_500_000_000
def now(): return datetime.datetime.now(datetime.timezone.utc).isoformat(timespec='seconds')
def memavail():
    for l in open('/proc/meminfo'):
        if l.startswith('MemAvailable'): return int(l.split()[1]) * 1024
def size():
    try: return max(1, int(open(os.path.join(POOL, 'size')).read().split()[0]))
    except Exception: return 1
def log(msg):
    with open(os.path.join(POOL, 'pool.log'), 'a') as f:
        fcntl.flock(f, fcntl.LOCK_EX); f.write(f'{now()}\t{msg}\n'); fcntl.flock(f, fcntl.LOCK_UN)
def acquire(label):
    while True:
        if memavail() >= MEM_FLOOR:
            for i in range(size()):
                fd = os.open(os.path.join(POOL, f'slot{i}'), os.O_CREAT | os.O_RDWR)
                try:
                    fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
                except BlockingIOError:
                    os.close(fd); continue
                log(f'ACQUIRE\tslot{i}\tsize={size()}\tmemavail={memavail()}\t{label}')
                return fd, i
        time.sleep(1.5)
def release(fd, i, label, rc, maxrss_kb):
    log(f'RELEASE\tslot{i}\trc={rc}\tmaxrss_kb={maxrss_kb}\tmemavail={memavail()}\t{label}')
    fcntl.flock(fd, fcntl.LOCK_UN); os.close(fd)
def run(label, argv, cwd=None, env=None, stdout=None):
    """Run argv under one pool slot; returns (rc, maxrss_kb, seconds)."""
    fd, i = acquire(label)
    t0 = time.time()
    try:
        p = subprocess.Popen(argv, cwd=cwd, env=env, stdout=stdout, stderr=subprocess.STDOUT if stdout else None)
        _, st, ru = os.wait4(p.pid, 0)
        rc = os.waitstatus_to_exitcode(st)
    finally:
        pass
    release(fd, i, label, rc, ru.ru_maxrss)
    return rc, ru.ru_maxrss, round(time.time() - t0, 2)
