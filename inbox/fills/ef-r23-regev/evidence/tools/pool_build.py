"""Dependency-ordered pool build: one scripts/lean_check_tree.sh call per module.
usage: python3 -I pool_build.py <repo> <order-file> <pool> <logdir> [--skip-built]
Env TCSLIB_OLEANS selects the olean tree. Stops scheduling on the first failure."""
import os, sys, subprocess, time
repo, order_file, pool, logdir = sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.argv[4]
skip = '--skip-built' in sys.argv
os.makedirs(logdir, exist_ok=True)
mods = [l.strip() for l in open(order_file) if l.strip()]
modset = set(mods)
def deps(m):
    out = []
    for line in open(os.path.join(repo, m + '.lean')):
        s = line.strip()
        if s.startswith('import '):
            i = s.split()[1].replace('.', '/')
            if i in modset: out.append(i)
    return out
D = {m: deps(m) for m in mods}
ol = os.environ.get('TCSLIB_OLEANS', os.path.join(repo, '.lake/tcslib-check-oleans'))
done, failed, running = set(), [], {}
if skip:
    for m in mods:
        if os.path.exists(os.path.join(ol, m + '.olean')): done.add(m)
summary = open(os.path.join(logdir, 'summary.tsv'), 'a')
pending = [m for m in mods if m not in done]
def ts(): return time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())
while pending or running:
    if not failed:
        for m in list(pending):
            if len(running) >= pool: break
            if all(d in done for d in D[m]):
                lf = open(os.path.join(logdir, m.replace('/', '.') + '.log'), 'w')
                p = subprocess.Popen(['bash', 'scripts/lean_check_tree.sh', m], cwd=repo,
                                     stdout=lf, stderr=subprocess.STDOUT)
                running[p.pid] = (m, time.time(), ts(), lf)
                pending.remove(m)
    if not running:
        break
    pid, status, ru = os.wait4(-1, 0)
    if pid not in running: continue
    m, t0, start, lf = running.pop(pid)
    lf.close()
    rc = os.waitstatus_to_exitcode(status)
    summary.write(f"{m}\t{rc}\t{start}\t{ts()}\t{time.time()-t0:.1f}s\tmaxrss_kb={ru.ru_maxrss}\n")
    summary.flush()
    if rc == 0: done.add(m)
    else: failed.append(m)
print('done', len(done), 'failed', failed, 'unscheduled', len(pending))
sys.exit(1 if failed or pending else 0)
