#!/usr/bin/env python3
"""Dependency-ordered Lean pool (gsw-6b-u12): check the modules of ORDER, each through
scripts/lean_check_tree.sh (one call per module), at most POOL at once, a module started only when
every module of ORDER it imports has a row with rc 0. Resumable: modules with an rc-0 row are skipped;
a failed row stops the run. Each module's log: LOGDIR/<module>.log; max RSS from os.wait4's rusage (the largest process of
the module's process tree, KiB).
TSV row: module, rc, errors (both forms), sorry warnings, start, end, wall s, max RSS KiB.
usage: pool.py REPO ORDER TSV LOGDIR POOL POOLLOG"""
import os, re, subprocess, sys, time, datetime
repo, order_f, tsv, logdir, pool, poollog = sys.argv[1:7]
pool = int(pool)
os.makedirs(logdir, exist_ok=True)
order = [l.strip() for l in open(order_f) if l.strip()]
S = set(order)
def imports(m):
    out = []
    for l in open(f'{repo}/{m}.lean', encoding='utf-8'):
        mm = re.match(r'^import\s+(TCSlib\S*)', l)
        if mm:
            d = mm.group(1).replace('.', '/')
            if d in S: out.append(d)
    return out
deps = {m: imports(m) for m in order}
done = set()
if os.path.exists(tsv):
    for l in open(tsv):
        p = l.rstrip('\n').split('\t')
        if len(p) > 1 and p[1] == '0': done.add(p[0])
        elif len(p) > 1: print('FAILED earlier:', p[0]); sys.exit(1)
ERR = re.compile(r'^\S+\.lean:\d+:\d+: error[:(]', re.M)
SOR = re.compile(r"declaration uses 'sorry'")
now = lambda: datetime.datetime.now(datetime.timezone.utc).strftime('%Y-%m-%dT%H:%M:%SZ')
def plog(s):
    with open(poollog, 'a') as f: f.write(f'{now()} {s}\n')
mem = lambda: int([l for l in open('/proc/meminfo') if l.startswith('MemAvailable')][0].split()[1])
plog(f'start pool={pool} nproc={os.cpu_count()} MemAvailable={mem()} kB order={order_f} done={len(done)}/{len(order)}')
running = {}
env = dict(os.environ, PATH=os.path.expanduser('~/.elan/bin') + ':' + os.environ['PATH'])
fail = False
peak_used = 0
total = int([l for l in open('/proc/meminfo') if l.startswith('MemTotal')][0].split()[1])
while True:
    for m, (p, st, lg) in list(running.items()):
        pid, status, ru = os.wait4(p.pid, os.WNOHANG)
        if pid:
            rc = os.waitstatus_to_exitcode(status)
            with open(lg, 'a') as f: f.write(f'END {m} {now()} rc={rc} maxrss_kib={ru.ru_maxrss}\n')
            txt = open(lg, encoding='utf-8', errors='replace').read()
            errs = len(ERR.findall(txt)); sor = len(SOR.findall(txt))
            with open(tsv, 'a') as f:
                f.write(f'{m}\t{rc}\t{errs}\t{sor}\t{st}\t{now()}\t{time.time()-p.t0:.1f}\t'
                        f'{ru.ru_maxrss}\n')
            del running[m]
            if rc == 0 and errs == 0: done.add(m)
            else: fail = True; plog(f'FAIL {m} rc={rc} errors={errs}')
    peak_used = max(peak_used, total - mem())
    if fail and not running: plog(f'stop on failure; peak used {peak_used} kB'); sys.exit(1)
    todo = [m for m in order if m not in done and m not in running]
    if not todo and not running:
        plog(f'DONE {len(done)}/{len(order)}; peak used {peak_used} kB'); print('DONE'); sys.exit(0)
    if not fail:
        for m in todo:
            if len(running) >= pool: break
            if all(d in done for d in deps[m]):
                if mem() < 2_100_000 and running: break
                lg = f'{logdir}/{m.replace("/", ".")}.log'
                st = now()
                with open(lg, 'w') as f:
                    f.write(f'START {m} {st}\n'); f.flush()
                    p = subprocess.Popen(['bash', 'scripts/lean_check_tree.sh', m],
                                         cwd=repo, stdout=f, stderr=subprocess.STDOUT, env=env)
                p.t0 = time.time()
                running[m] = (p, st, lg)
    time.sleep(0.5)
