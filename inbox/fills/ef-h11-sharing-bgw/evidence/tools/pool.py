# Dependency-ordered pool: runs scripts/lean_check_tree.sh once per module, at most N at a time.
# usage: python3 -I pool.py <repo> <order-file> <logdir> <N> [--force mod,...]
import sys, os, re, subprocess, time
repo, orderf, logdir, N = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4])
order = [l.strip() for l in open(orderf) if l.strip()]
OL = os.environ['TCSLIB_OLEANS']
os.makedirs(logdir, exist_ok=True)
def deps(m):
    out = []
    for line in open(os.path.join(repo, m + '.lean')):
        mm = re.match(r'^import\s+(TCSlib\S*)', line)
        if mm: out.append(mm.group(1).replace('.', '/'))
    return out
D = {m: [d for d in deps(m) if d in order] for m in order}
done, failed, running = set(), set(), {}
pending = list(order)
summ = open(os.path.join(logdir, 'pool-summary.txt'), 'a')
while pending or running:
    for m, (p, t0, lf) in list(running.items()):
        rc = p.poll()
        if rc is not None:
            lf.close(); del running[m]
            log = open(os.path.join(logdir, m.replace('/', '.') + '.log')).read()
            errs = len(re.findall(r'^\S+\.lean:\d+:\d+: error[:(]', log, re.M))
            sor = log.count("declaration uses 'sorry'")
            rss = re.search(r'Maximum resident set size \(kbytes\): (\d+)', log)
            line = f"{m}\trc={rc}\terrors={errs}\tsorry={sor}\tsec={time.time()-t0:.0f}\tmaxrss_kb={rss.group(1) if rss else '?'}"
            print(line, flush=True); summ.write(line + '\n'); summ.flush()
            (done if rc == 0 else failed).add(m)
    for m in list(pending):
        if len(running) >= N: break
        if any(d in failed for d in D[m]):
            pending.remove(m); failed.add(m); print(f"{m}\tSKIPPED (dep failed)", flush=True); continue
        if all(d in done for d in D[m]):
            pending.remove(m)
            lf = open(os.path.join(logdir, m.replace('/', '.') + '.log'), 'w')
            lf.write(f"# start {time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())}\n"); lf.flush()
            p = subprocess.Popen(['/usr/bin/time', '-v', 'bash', 'scripts/lean_check_tree.sh', m],
                                 cwd=repo, stdout=lf, stderr=subprocess.STDOUT)
            running[m] = (p, time.time(), lf)
            print(f"START {m} pid={p.pid}", flush=True)
    time.sleep(1)
print("POOL-DONE failed=%d" % len(failed), flush=True)
