"""pfr_build.py <modules-file> <tree> <logdir> (gsw-6b-statements, new; the 6a statement job's
precedent, "PFR's 31 modules were compiled with plain lean -o into the worker's own olean tree"):
compile each PFR module (dotted names, dependency order) from .lake/packages/PFR with
`lean <file> -o <tree>/PFR/....olean`, LEAN_PATH = <tree> plus the packages' build dirs, one at a
time under a pool slot; stale olean removed first; rc, error count and a fresh olean required."""
import sys, os, re, glob, subprocess
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import poollib
mf, tree, logdir = sys.argv[1:4]
os.makedirs(logdir, exist_ok=True)
pfr = '/home/user/w6b/.lake/packages/PFR'
lp = ':'.join([tree] + sorted(glob.glob('/home/user/w6b/.lake/packages/*/.lake/build/lib/lean')))
env = dict(os.environ, LEAN_PATH=lp, PATH=os.path.expanduser('~/.elan/bin') + ':' + os.environ['PATH'])
bad = 0
with open(os.path.join(logdir, 'summary.tsv'), 'a') as summ:
    for m in [l.strip() for l in open(mf) if l.strip() and not l.startswith('#')]:
        rel = m.replace('.', '/'); out = os.path.join(tree, rel + '.olean')
        os.makedirs(os.path.dirname(out), exist_ok=True)
        if os.path.exists(out): os.remove(out)
        lf = os.path.join(logdir, m + '.log')
        with open(lf, 'wb') as o:
            rc, rss, sec = poollib.run('pfr:' + m, ['lean', rel + '.lean', '-o', out], cwd=pfr, env=env, stdout=o)
        txt = open(lf, encoding='utf-8', errors='replace').read()
        errs = len(re.findall(r'^\S+\.lean:\d+:\d+: error[:(]', txt, re.M))
        ok = rc == 0 and errs == 0 and os.path.getsize(out) > 0 if os.path.exists(out) else False
        bad += not ok
        summ.write(f'{m}\trc={rc}\terrors={errs}\tolean={"fresh" if ok else "MISSING"}\t{sec}\tmaxrss_kb={rss}\n'); summ.flush()
        if not ok: break
print('PFR', 'OK' if not bad else 'FAIL')
