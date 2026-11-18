"""pool.py <repo> <order.txt> <N> <logdir> : compile modules with scripts/lean_check_tree.sh in
dependency order, at most N at once; a module starts only when all its TCSlib imports are done.
Writes <logdir>/<mod>.log, and a summary line per module to <logdir>/pool-run.tsv."""
import sys, os, subprocess, time, threading, re
repo, order_f, N, logdir = sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.argv[4]
os.makedirs(logdir, exist_ok=True)
order = [l.strip() for l in open(order_f) if l.strip()]
inset = set(order)
def imps(m):
    out = []
    for l in open(os.path.join(repo, m + '.lean'), encoding='utf-8'):
        s = l.strip()
        if s.startswith('import '):
            i = s.split()[1].replace('.', '/')
            if i in inset: out.append(i)
    return out
deps = {m: imps(m) for m in order}
done, failed, running = set(), set(), {}
summ = open(os.path.join(logdir, 'pool-run.tsv'), 'a')
lock = threading.Lock()
env = dict(os.environ); env['PATH'] = os.path.expanduser('~/.elan/bin') + ':' + env['PATH']
def run(m):
  try:
    run1(m)
  except Exception as ex:
    with lock:
        failed.add(m); running.pop(m, None); summ.write(f"{m}\tEXC {ex}\n")
def run1(m):
    lf = os.path.join(logdir, m.replace('/', '.') + '.log')
    t0 = time.time()
    with open(lf, 'w') as f:
        p = subprocess.Popen(['bash', 'scripts/lean_check_tree.sh', m], cwd=repo,
                             stdout=f, stderr=subprocess.STDOUT, env=env)
        _, status, ru = os.wait4(p.pid, 0)
        p.returncode = os.waitstatus_to_exitcode(status)
    r = p
    txt = open(lf).read()
    rss = ru.ru_maxrss
    errs = len(re.findall(r'^\S+\.lean:\d+:\d+: error[:(]', txt, re.M))
    sor = txt.count("declaration uses 'sorry'")
    with lock:
        summ.write(f"{m}\t{r.returncode}\t{errs}\t{sor}\t{time.strftime('%H:%M:%S', time.gmtime(t0))}\t{time.time()-t0:.0f}s\t{rss}KB\n"); summ.flush()
        (done if r.returncode == 0 else failed).add(m)
        running.pop(m, None)
while True:
    with lock:
        if failed: break
        pending = [m for m in order if m not in done and m not in running]
        if not pending and not running: break
        ready = [m for m in pending if all(d in done for d in deps[m])]
        while ready and len(running) < N:
            m = ready.pop(0)
            th = threading.Thread(target=run, args=(m,)); running[m] = th; th.start()
    time.sleep(0.5)
for th in list(running.values()): th.join()
print('done', len(done), 'failed', sorted(failed))
