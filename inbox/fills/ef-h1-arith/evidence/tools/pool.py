# Dependency-ordered pool build: python3 -I pool.py <repo> <order-file> <logdir> <olean-tree> <N>
import sys, os, re, subprocess, time
repo, order, logdir, tree, N = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4], int(sys.argv[5])
mods = [l.strip() for l in open(order) if l.strip()]
os.makedirs(logdir, exist_ok=True)
def deps(m):
    out = []
    for line in open(os.path.join(repo, m + '.lean'), encoding='utf-8'):
        mm = re.match(r'^import\s+(\S+)', line)
        if mm and mm.group(1).startswith('TCSlib'):
            out.append(mm.group(1).replace('.', '/'))
    return [d for d in out if d in set(mods)]
D = {m: deps(m) for m in mods}
done, failed, running = set(), set(), {}
summary = open(os.path.join(logdir, 'pool-summary.tsv'), 'a')
env = dict(os.environ, TCSLIB_OLEANS=tree)
def memavail():
    for l in open('/proc/meminfo'):
        if l.startswith('MemAvailable'): return int(l.split()[1]) // 1024
peak = 0
while True:
    for m, (p, t0, lf) in list(running.items()):
        if p.poll() is not None:
            lf.close(); del running[m]
            txt = open(os.path.join(logdir, m.replace('/', '.') + '.log'), encoding='utf-8', errors='replace').read()
            errs = len(re.findall(r'^\S+\.lean:\d+:\d+: error[:(]', txt, re.M))
            sor = txt.count("declaration uses 'sorry'")
            rss = re.search(r'Maximum resident set size \(kbytes\): (\d+)', txt)
            rss = int(rss.group(1)) // 1024 if rss else -1
            ok = p.returncode == 0
            (done if ok else failed).add(m)
            summary.write(f"{m}\t{p.returncode}\t{errs}\t{sor}\t{rss}MiB\t{time.time()-t0:.1f}s\n"); summary.flush()
            print(f"{'OK ' if ok else 'FAIL'} {m} rc={p.returncode} err={errs} rss={rss}MiB {time.time()-t0:.0f}s", flush=True)
    peak = max(peak, 15000 - (memavail() or 0))
    blocked = {m for m in mods if any(d in failed for d in D[m])}
    pending = [m for m in mods if m not in done and m not in failed and m not in running and m not in blocked]
    if not pending and not running: break
    for m in pending:
        if len(running) >= N: break
        if all(d in done for d in D[m]):
            lf = open(os.path.join(logdir, m.replace('/', '.') + '.log'), 'w')
            p = subprocess.Popen(['python3', '-I', '/home/user/scripts/timev.py', 'bash', 'scripts/lean_check_tree.sh', m], cwd=repo, env=env, stdout=lf, stderr=subprocess.STDOUT)
            running[m] = (p, time.time(), lf)
            print(f"START {m} pid={p.pid} running={len(running)} memavail={memavail()}MiB", flush=True)
    time.sleep(0.5)
print(f"done={len(done)} failed={len(failed)} blocked={len([m for m in mods if any(d in failed for d in D[m])])} total={len(mods)}")
