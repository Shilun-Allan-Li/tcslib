# Dependency-ordered pool build over lean_check_tree.sh. Usage:
# python3 -I pool.py <repo> <order-file> <oleans> <logdir> <poolsize> [--skip-fresh]
import sys, os, re, subprocess, time, threading
repo, orderf, ol, logdir, n = sys.argv[1:6]; n = int(n)
order = [l.strip() for l in open(orderf) if l.strip()]
os.makedirs(logdir, exist_ok=True)
def deps(m):
    out = []
    for line in open(os.path.join(repo, m + '.lean')):
        mm = re.match(r'^import\s+(\S+)', line)
        if mm and mm.group(1).startswith('TCSlib'): out.append(mm.group(1).replace('.', '/'))
    return out
D = {m: [d for d in deps(m) if d in order] for m in order}
done, failed, running = set(), set(), {}
lock = threading.Lock()
summary = open(os.path.join(logdir, 'summary.tsv'), 'a')
env = dict(os.environ, TCSLIB_OLEANS=ol)
def run(m):
    log = os.path.join(logdir, m.replace('/', '.') + '.log')
    t0 = time.time()
    with open(log, 'w') as f:
        pr = subprocess.Popen(['/home/user/work/tools/lean_slot.sh', os.path.abspath(repo), m],
                              cwd=repo, env=env, stdout=f, stderr=subprocess.STDOUT)
        _, st, ru = os.wait4(pr.pid, 0)
        rc = os.waitstatus_to_exitcode(st)
        f.write(f"\n[pool] start={t0:.0f} end={time.time():.0f} maxrss_kB={ru.ru_maxrss} rc={rc}\n")
    class P: pass
    p = P(); p.returncode = rc
    txt = open(log).read()
    rss = re.search(r'maxrss_kB=(\d+)', txt)
    errs = len(re.findall(r'^\S+\.lean:\d+:\d+: error[:(]', txt, re.M))
    sor = txt.count("declaration uses 'sorry'")
    with lock:
        summary.write(f"{m}\t{p.returncode}\t{errs}\t{sor}\t{rss.group(1) if rss else '?'}\t{time.time()-t0:.1f}\n"); summary.flush()
        (done if p.returncode == 0 else failed).add(m); running.pop(m, None)
    print(m, p.returncode, f"{time.time()-t0:.0f}s", flush=True)
pending = list(order)
while pending or running:
    with lock:
        blocked = [m for m in pending if any(d in failed for d in D[m])]
        for m in blocked: pending.remove(m); failed.add(m); print('SKIP', m, flush=True)
        ready = [m for m in pending if all(d in done for d in D[m])]
        while ready and len(running) < n:
            m = ready.pop(0); pending.remove(m)
            th = threading.Thread(target=run, args=(m,)); running[m] = th; th.start()
    time.sleep(0.5)
print('DONE', len(done), 'FAILED', len(failed))
