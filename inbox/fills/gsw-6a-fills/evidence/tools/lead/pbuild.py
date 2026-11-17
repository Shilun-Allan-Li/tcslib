"""pbuild.py <worktree> <modules-file> <tree> <logdir> (gsw-6a-fills, new; replaces the statement job's
sweep.py, which ran one module at a time under a host lock): check the modules of <modules-file> (repo paths
without .lean, in import order) through `bash scripts/lean_check_tree.sh <module>` with TCSLIB_OLEANS=<tree>,
each under one slot of the shared Lean pool (poollib.py), in dependency order: a module starts only when every
TCSlib module it imports that is in the list has passed (imports outside the list must already have an olean in
<tree>); a module whose prerequisite failed is not started (SKIPPED-DEP). One process per module, one tree per
agent, so no two processes write one file. Writes <logdir>/mods/<module>.log and appends to
<logdir>/summary.tsv: module, rc, errors (G26-N1 `^\\S+\\.lean:\\d+:\\d+: error[:(]`), lines containing
"error:", sorry warnings, the declarations they name (source line at the warning), start, end, seconds, max
RSS (KiB, wait4), the source SHA-256 at start and at end."""
import sys, os, re, time, hashlib, threading, datetime
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import poollib
wt, mf, tree, logdir = [os.path.abspath(a) for a in sys.argv[1:5]]
os.makedirs(os.path.join(logdir, 'mods'), exist_ok=True)
mods = [l.strip() for l in open(mf) if l.strip() and not l.startswith('#')]
mset = set(mods)
def imports(m):
    out = []
    for l in open(os.path.join(wt, m + '.lean'), encoding='utf-8'):
        r = re.match(r'^import\s+(TCSlib\S*)', l)
        if r: out.append(r.group(1).replace('.', '/'))
    return out
deps = {}
for m in mods:
    deps[m] = [d for d in imports(m) if d in mset]
    for d in imports(m):
        if d not in mset and not os.path.exists(os.path.join(tree, d + '.olean')):
            sys.exit(f'missing prerequisite olean {d} for {m}')
sha = lambda p: hashlib.sha256(open(p, 'rb').read()).hexdigest()
now = lambda: datetime.datetime.now(datetime.timezone.utc).isoformat(timespec='seconds')
env = dict(os.environ); env['TCSLIB_OLEANS'] = tree
env['PATH'] = os.path.expanduser('~/.elan/bin') + ':' + env.get('PATH', '')
state = {}; lock = threading.Lock(); summ = open(os.path.join(logdir, 'summary.tsv'), 'a')
DECL = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec)\s+)*'
                  r'(?:theorem|lemma|def|abbrev|instance|example)\s+(\S+)')
def sorry_decls(m, txt):
    src = open(os.path.join(wt, m + '.lean'), encoding='utf-8').read().split('\n'); names = []
    for r in re.finditer(r"^\S+\.lean:(\d+):\d+: warning: declaration uses 'sorry'", txt, re.M):
        line = src[int(r.group(1)) - 1]; d = DECL.match(line)
        names.append(d.group(1) if d else f'?line{r.group(1)}')
    return names
def build(m):
    lp = os.path.join(logdir, 'mods', m.replace('/', '_') + '.log')
    s0 = sha(os.path.join(wt, m + '.lean')); t0 = now()
    with open(lp, 'wb') as out:
        rc, rss, sec = poollib.run(f'{os.path.basename(logdir)}:{m}', ['bash', 'scripts/lean_check_tree.sh', m],
                                   cwd=wt, env=env, stdout=out)
    txt = open(lp, encoding='utf-8', errors='replace').read()
    errs = len(re.findall(r'^\S+\.lean:\d+:\d+: error[:(]', txt, re.M))
    errl = sum(1 for l in txt.split('\n') if 'error:' in l)
    names = sorry_decls(m, txt)
    s1 = sha(os.path.join(wt, m + '.lean'))
    with lock:
        summ.write('\t'.join(map(str, [m, f'rc={rc}', f'errors={errs}', f'error_lines={errl}', f'sorry={len(names)}',
                   'decls=' + ','.join(names), t0, now(), sec, f'maxrss_kb={rss}', s0, s1])) + '\n'); summ.flush()
        state[m] = 'ok' if (rc == 0 and errs == 0 and errl == 0 and s0 == s1) else 'fail'
running = {}
while len(state) < len(mods):
    with lock:
        for m in mods:
            if m in state or m in running: continue
            if any(state.get(d) in ('fail', 'skip') for d in deps[m]):
                state[m] = 'skip'; summ.write(f'{m}\tSKIPPED-DEP\n'); summ.flush(); continue
            if all(state.get(d) == 'ok' for d in deps[m]) and len(running) < 16:
                t = threading.Thread(target=build, args=(m,)); running[m] = t; t.start()
    for m, t in list(running.items()):
        if not t.is_alive(): t.join(); del running[m]
    time.sleep(0.5)
for t in running.values(): t.join()
bad = [m for m in mods if state[m] != 'ok']
print(f'RESULT modules={len(mods)} ok={len(mods) - len(bad)} not_ok={len(bad)}')
for m in bad: print('NOT-OK', m, state[m])
summ.write(f'# done {now()} {mf} ok={len(mods) - len(bad)}/{len(mods)}\n')
