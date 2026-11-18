#!/usr/bin/env python3
"""Pool build: check every module of <list> through tools/check.sh (one scripts/lean_check_tree.sh
call per module), at most <pool> Lean processes at once, in dependency order (a module starts only
when every module of the list it imports has passed). Resumable: a module whose per-module log
ends with status=0 and whose recorded source SHA-256 equals the current source is skipped.

Usage: python3 -I pool_build.py <list> <logdir> <aggregate log> <pool> <pool.log>
The aggregate log is the concatenation of the per-module logs in list order (rewritten at the end
and after each completion). Stops launching after the first failure."""
import sys, os, re, subprocess, time, hashlib

lst, logdir, agg, pool, poollog = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4]), sys.argv[5]
WT = os.environ.get('WT', '/workspace/u13')
mods = [l.strip() for l in open(lst) if l.strip()]
inlist = set(mods)
os.makedirs(logdir, exist_ok=True)

def src(m): return os.path.join(WT, m + '.lean')
def sha(m): return hashlib.sha256(open(src(m), 'rb').read()).hexdigest()
def lp(m): return os.path.join(logdir, m.replace('/', '__') + '.log')
def deps(m):
    out = []
    for line in open(src(m)):
        mm = re.match(r'^import\s+(TCSlib\S*)', line)
        if mm:
            d = mm.group(1).replace('.', '/')
            if d in inlist: out.append(d)
    return out
def ok(m):
    p = lp(m)
    if not os.path.exists(p) or not os.path.exists(p + '.sha'): return False
    t = open(p).read().rstrip().split('\n')
    return bool(t) and t[-1].endswith('status=0') and open(p + '.sha').read().strip() == sha(m)
def memavail():
    for l in open('/proc/meminfo'):
        if l.startswith('MemAvailable'): return int(l.split()[1]) * 1024
def plog(msg):
    with open(poollog, 'a') as f: f.write(time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()) + ' ' + msg + '\n')
def aggregate():
    with open(agg, 'w') as f:
        for m in mods:
            if os.path.exists(lp(m)): f.write(open(lp(m)).read())

D = {m: deps(m) for m in mods}
done = {m for m in mods if ok(m)}
plog(f'start list={lst} modules={len(mods)} already-done={len(done)} pool={pool} nproc={os.cpu_count()} MemAvailable={memavail()}')
running = {}
failed = None
peak = 0
while True:
    for m, (pr, s) in list(running.items()):
        if pr.poll() is not None:
            del running[m]
            t = open(lp(m)).read().rstrip().split('\n')
            if t and t[-1].endswith('status=0'):
                open(lp(m) + '.sha', 'w').write(s + '\n'); done.add(m)
            else:
                failed = m; plog(f'FAIL {m}')
            aggregate()
    if failed is None:
        for m in mods:
            if len(running) >= pool: break
            if m in done or m in running: continue
            if all(d in done for d in D[m]):
                if os.path.exists(lp(m)): os.remove(lp(m))
                s = sha(m)
                pr = subprocess.Popen(['/workspace/u13-tools/check.sh', m, lp(m)])
                running[m] = (pr, s)
    peak = max(peak, len(running))
    if not running:
        break
    time.sleep(2)
aggregate()
plog(f'end done={len(done)}/{len(mods)} failed={failed} peak-concurrency={peak} MemAvailable={memavail()}')
print('POOL-BUILD', 'FAILED at ' + failed if failed else ('COMPLETE' if len(done) == len(mods) else 'INCOMPLETE'),
      f'{len(done)}/{len(mods)}')
