#!/usr/bin/env python3
"""Dependency-ordered pool runner for scripts/lean_check_tree.sh (gsw-6b-u18-u19).

Usage: python3 -I sweep.py ORDER POOL LOGDIR [REPO]
Runs each module of ORDER (module paths without .lean) through lean_check_tree.sh with at most
POOL processes, starting a module only after every TCSlib import of it that is in ORDER has
passed. Writes LOGDIR/<module with / -> .>.log and LOGDIR/sweep.tsv
(module, rc, start, end, seconds, maxrss_kB, errors, errors_paren, sorry_warnings).
TCSLIB_OLEANS is taken from the environment.
"""
import os, re, sys, time, subprocess

order_file, pool, logdir = sys.argv[1], int(sys.argv[2]), sys.argv[3]
repo = sys.argv[4] if len(sys.argv) > 4 else os.getcwd()
mods = [l.strip() for l in open(order_file) if l.strip() and not l.startswith('#')]
mset = set(mods)
deps = {}
for m in mods:
    ds = []
    for line in open(os.path.join(repo, m + '.lean'), encoding='utf-8'):
        mm = re.match(r'^import\s+(\S+)', line)
        if mm:
            d = mm.group(1).replace('.', '/')
            if d in mset:
                ds.append(d)
    deps[m] = ds
os.makedirs(logdir, exist_ok=True)
status = {}
running = {}
# resume: modules already recorded with rc 0 whose olean exists are done
tsv_path = os.path.join(logdir, 'sweep.tsv')
if os.path.exists(tsv_path):
    ol = os.environ.get('TCSLIB_OLEANS', os.path.join(repo, '.lake/tcslib-check-oleans'))
    for l in open(tsv_path):
        f = l.rstrip('\n').split('\t')
        if len(f) > 1 and f[1] == '0' and os.path.exists(os.path.join(ol, f[0] + '.olean')):
            status[f[0]] = 0
pending = [m for m in mods if status.get(m) != 0]
tsv = open(os.path.join(logdir, 'sweep.tsv'), 'a')
err1 = re.compile(r'^\S+\.lean:\d+:\d+: error:', re.M)
err2 = re.compile(r'^\S+\.lean:\d+:\d+: error[:(]', re.M)
def ts():
    return time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())
failed = False
while pending or running:
    progressed = False
    for m in list(pending):
        if len(running) >= pool or failed:
            break
        if any(status.get(d) != 0 for d in deps[m]):
            if any(status.get(d) not in (None, 0) for d in deps[m]):
                pending.remove(m); status[m] = 'skipped'
                tsv.write(f"{m}\tSKIPPED\t\t\t\t\t\t\t\n"); tsv.flush()
            continue
        lf = open(os.path.join(logdir, m.replace('/', '.') + '.log'), 'w')
        p = subprocess.Popen(['bash', 'scripts/lean_check_tree.sh', m], cwd=repo, stdout=lf,
                             stderr=subprocess.STDOUT)
        running[p.pid] = (m, lf, ts(), time.time(), p)
        pending.remove(m)
        progressed = True
    if not running:
        if pending and failed:
            for m in pending:
                tsv.write(f"{m}\tNOT-RUN\t\t\t\t\t\t\t\n")
            pending = []
        continue
    pid, st, ru = os.wait4(-1, 0)
    if pid not in running:
        continue
    m, lf, start, t0, _p = running.pop(pid)
    _p.returncode = os.waitstatus_to_exitcode(st)
    lf.close()
    rc = os.waitstatus_to_exitcode(st)
    txt = open(lf.name, encoding='utf-8', errors='replace').read()
    e1 = len(err1.findall(txt)); e2 = len(err2.findall(txt))
    sw = txt.count("declaration uses 'sorry'")
    status[m] = rc
    tsv.write(f"{m}\t{rc}\t{start}\t{ts()}\t{time.time()-t0:.1f}\t{ru.ru_maxrss}\t{e1}\t{e2}\t{sw}\n")
    tsv.flush()
    if rc != 0 and os.environ.get('SWEEP_STOP_ON_FAIL', '1') == '1':
        failed = True
print('done', sum(1 for v in status.values() if v == 0), 'ok of', len(mods))
