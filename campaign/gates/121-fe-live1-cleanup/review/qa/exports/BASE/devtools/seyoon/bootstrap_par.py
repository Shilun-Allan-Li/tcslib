"""bootstrap_par.py <worktree dir> <snapshot name> [<workers>]: continue a bootstrap
(`bootstrap-snapshot.sh`) with up to <workers> (default 2) modules compiling at once.

The bootstrap's order list and log must exist (start it with `bootstrap-snapshot.sh`). Checks as
`--resume`: the worktree's `TCSlib/` and `TCSlib.lean` are clean and equal to the log's commit's,
the order list is what `bootstrap_order.py` gives now, and every module logged `exit=0` has a
non-empty olean. Then a module starts only when every TCSlib module it imports is logged
`exit=0`, in the order list's order among the ready ones, each through
`scripts/lean_check_tree.sh` under `nice -n 10` (never `lake build`). Each worker holds one of the
two machine-wide Lean slots (`$TCSLIB_SCRATCH/locks/lean-slot-{1,2}`, the protocol of
`leanelab.sh`) while its module compiles, so this tool and `leanelab.sh` together never run more
than two Lean processes. Log lines keep the bootstrap's format, in completion order. A failure
stops new starts, lets running modules finish, and logs `# stopped at <module>`. On completion
the last line is exactly `# modules=N failed=0`. Re-running the same command resumes."""
import os
import re
import subprocess
import sys
import threading
import time

S = os.environ.get('TCSLIB_SCRATCH', os.path.expanduser('~/.tcslib-scratch'))
WT, NAME = os.path.join(S, sys.argv[1]), sys.argv[2]
W = int(sys.argv[3]) if len(sys.argv) > 3 else 2
T = os.path.dirname(os.path.abspath(__file__))
O = os.path.join(S, NAME)
LIST = os.path.join(S, 'fills/replay', f'order-{NAME}.txt')
LOG = os.path.join(S, 'fills/replay', f'bootstrap-{NAME}.log')
SKIP = os.path.join(S, 'fills/replay', f'skipped-{NAME}.txt')
LOCKS = os.path.join(S, 'locks')


def die(msg):
    sys.exit(f'bootstrap_par: {msg}')


def git(*a):
    return subprocess.run(['git', '-C', WT, *a], capture_output=True, text=True).stdout.strip()


for p in (LIST, LOG):
    if not os.path.isfile(p):
        die(f'missing {p}: start with bootstrap-snapshot.sh')
log = open(LOG, encoding='utf-8').read().splitlines()
if any(l.startswith('# modules=') for l in log):
    print(f'{NAME} is complete: {log[-1]}')
    sys.exit(0)
m0 = re.match(r'# bootstrap \S+ at ([0-9a-f]{40}) ', log[0])
if not m0:
    die("no commit on the log's first line")
for p in ('TCSlib', 'TCSlib.lean'):
    if git('rev-parse', f'{m0.group(1)}:{p}') != git('rev-parse', f'HEAD:{p}'):
        die(f'{p} at HEAD differs from {m0.group(1)}')
if git('status', '--porcelain', '--', 'TCSlib', 'TCSlib.lean'):
    die(f'uncommitted Lean changes in {WT}')
fresh = subprocess.run(['python3', '-I', os.path.join(T, 'bootstrap_order.py'), WT, SKIP + '.new'],
                       capture_output=True, text=True)
if fresh.returncode:
    die(fresh.stderr)
order = open(LIST).read().split()
if fresh.stdout.split() != order:
    die('the order list differs from bootstrap_order.py (use bootstrap-snapshot.sh --resume first)')
os.replace(SKIP + '.new', SKIP)
done = set()
for l in log:
    m = re.match(r'(\S+) exit=0 errors=', l)
    if m:
        done.add(m.group(1))
for m in done:
    ol = os.path.join(O, m + '.olean')
    if not os.path.isfile(ol) or os.path.getsize(ol) == 0:
        die(f'missing olean for logged {m}')
stopped = [l for l in log if l.startswith('# stopped')]
failed_logged = [re.match(r'(\S+) exit=', l).group(1) for l in log if re.match(r'\S+ exit=[1-9]', l)]
if stopped and any(f in order for f in failed_logged if f not in done):
    die('the run stopped on a module the order list still contains; start a new snapshot')

inorder = set(order)
imps = {}
for m in order:
    t = open(os.path.join(WT, m + '.lean'), encoding='utf-8').read()
    imps[m] = [i.replace('.', '/') for i in re.findall(r'^import\s+(TCSlib\S*)', t, re.M)
               if i != 'TCSlib' and i.replace('.', '/') in inorder]

lock = threading.Lock()
running, failed = set(), []
logf = open(LOG, 'a', encoding='utf-8')


def logline(s):
    with lock:
        logf.write(s + '\n')
        logf.flush()


def take_slot():
    os.makedirs(LOCKS, exist_ok=True)
    while True:
        for i in (1, 2):
            s = os.path.join(LOCKS, f'lean-slot-{i}')
            try:
                os.mkdir(s)
                with open(os.path.join(s, 'pid'), 'w') as f:
                    f.write(str(os.getpid()))
                return s
            except FileExistsError:
                try:
                    pid = open(os.path.join(s, 'pid')).read().strip()
                except OSError:
                    pid = ''
                stale = False
                if pid:
                    try:
                        os.kill(int(pid), 0)
                    except (OSError, ValueError):
                        stale = True
                elif time.time() - os.path.getmtime(s) > 60:
                    stale = True
                if stale:
                    try:
                        os.remove(os.path.join(s, 'pid'))
                    except OSError:
                        pass
                    try:
                        os.rmdir(s)
                    except OSError:
                        pass
        time.sleep(2)


def release(s):
    try:
        os.remove(os.path.join(s, 'pid'))
    except OSError:
        pass
    try:
        os.rmdir(s)
    except OSError:
        pass


def compile_one(m):
    slot = take_slot()
    try:
        env = dict(os.environ, TCSLIB_OLEANS=O)
        r = subprocess.run(['nice', '-n', '10', 'bash', 'scripts/lean_check_tree.sh', m], cwd=WT,
                           env=env, capture_output=True, text=True)
    finally:
        release(slot)
    out = r.stdout + r.stderr
    lines = out.splitlines()
    nerr = sum(1 for l in lines if 'error' in l)
    nsorry = sum(1 for l in lines if "declaration uses 'sorry'" in l)
    logline(f'{m} exit={r.returncode} errors={nerr} sorry={nsorry}')
    with lock:
        running.discard(m)
        if r.returncode == 0:
            done.add(m)
        else:
            failed.append(m)
            for l in [l for l in lines if 'error' in l][:5]:
                logf.write(l + '\n')
            logf.flush()


logline(f'# resumed after {len(done)} modules with up to {W} workers (bootstrap_par.py), at '
        f'{git("rev-parse", "HEAD")} (same Lean tree); {time.ctime()}')
threads = []
while True:
    with lock:
        todo = [m for m in order if m not in done and m not in running]
        if not todo and not running:
            break
        ready = [] if failed else [m for m in todo if all(i in done for i in imps[m])]
        start = ready[:max(0, W - len(running))]
        for m in start:
            running.add(m)
        busy = bool(running)
    if not busy and not failed and todo:
        logline('# stopped: no module is ready (an import is neither logged nor listed)')
        sys.exit(1)
    for m in start:
        t = threading.Thread(target=compile_one, args=(m,))
        t.start()
        threads.append(t)
    if failed and not busy:
        break
    time.sleep(1)
for t in threads:
    t.join()
if failed:
    logline(f'# stopped at {failed[0]}')
    sys.exit(1)
logline(f'# finished {time.ctime()}')
logline(f'# modules={len(order)} failed=0')
print(f'# modules={len(order)} failed=0')
