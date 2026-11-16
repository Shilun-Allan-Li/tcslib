#!/usr/bin/env python3
"""sweep.py <worktree> <modules-file> <logdir> [--skip <file>] [--pfr]
Check modules one at a time (in file order) through check.py's host-wide lock, against the worktree's
olean tree. With --pfr, the lines of <modules-file> are PFR package modules (dotted names): each is
compiled with `lean <file> -o <tree>/PFR/....olean` from `.lake/packages/PFR`, under the same lock, with
LEAN_PATH = <tree> + the lake packages' build dirs (nothing is written inside the package tree).
Writes <logdir>/mods/<module>.log, <logdir>/summary.txt (module, rc, errors, sorry warnings, start,
end, max RSS, source sha256). Stops at the first failure (later modules would be checked against
missing prerequisites)."""
import fcntl, glob, hashlib, os, re, resource, subprocess, sys, time
wt, mf, logdir = sys.argv[1], sys.argv[2], sys.argv[3]
skip = set()
if '--skip' in sys.argv:
    skip = {l.strip() for l in open(sys.argv[sys.argv.index('--skip') + 1]) if l.strip()}
pfr = '--pfr' in sys.argv
LOCK = '/home/user/gsw6a/.lean.lock'
env = dict(os.environ)
env['PATH'] = os.path.expanduser('~/.elan/bin') + ':' + env.get('PATH', '')
tree = env.get('TCSLIB_OLEANS', os.path.join(wt, '.lake/tcslib-check-oleans'))
os.makedirs(os.path.join(logdir, 'mods'), exist_ok=True)
now = lambda: time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())
summ = open(os.path.join(logdir, 'summary.txt'), 'a')
for m in [l.strip() for l in open(mf) if l.strip()]:
    if m in skip: continue
    if pfr:
        rel = m.replace('.', '/')
        cwd = os.path.join(wt, '.lake/packages/PFR'); src = os.path.join(cwd, rel + '.lean')
        out = os.path.join(tree, rel + '.olean'); os.makedirs(os.path.dirname(out), exist_ok=True)
        if os.path.exists(out): os.remove(out)
        lp = ':'.join([tree] + sorted(d for d in glob.glob(os.path.join(wt, '.lake/packages/*/.lake/build/lib/lean'))))
        e2 = dict(env); e2['LEAN_PATH'] = lp
        cmd = ['lean', rel + '.lean', '-o', out]
    else:
        cwd = wt; src = os.path.join(wt, m + '.lean'); e2 = env; out = None
        cmd = ['bash', 'scripts/lean_check_tree.sh', m]
    sha = hashlib.sha256(open(src, 'rb').read()).hexdigest()
    lp_ = os.path.join(logdir, 'mods', m.replace('/', '.') + '.log')
    with open(LOCK, 'w') as lk:
        fcntl.flock(lk, fcntl.LOCK_EX)
        t0 = now()
        with open(lp_, 'w') as fo:
            p = subprocess.Popen(cmd, cwd=cwd, env=e2, stdout=fo, stderr=subprocess.STDOUT)
            _, st, ru = os.wait4(p.pid, 0)
        t1 = now()
        fcntl.flock(lk, fcntl.LOCK_UN)
    rc = os.waitstatus_to_exitcode(st)
    txt = open(lp_, encoding='utf8', errors='replace').read()
    errs = len(re.findall(r'^\S+\.lean:\d+:\d+: error[:(]', txt, re.M))
    sor = txt.count("declaration uses 'sorry'")
    if pfr and (rc != 0 or not os.path.exists(out) or os.path.getsize(out) == 0): rc = rc or 1
    line = f'{m}\trc={rc}\terrors={errs}\tsorry={sor}\t{t0}\t{t1}\tmaxrss_kib={ru.ru_maxrss}\tsha256={sha}'
    summ.write(line + '\n'); summ.flush()
    if rc != 0 or errs:
        print('FAIL', line); sys.exit(1)
print('DONE', now())
