#!/usr/bin/env python3
"""One-module checker wrapper (cleanup-part2). Runs the unchanged scripts/lean_check_tree.sh on one
module, in the clone, with TCSLIB_OLEANS = the one tree, and records: command/cwd/tree/PATH mode,
source SHA-256, direct-prerequisite object identities (local/PFR from the tree, Mathlib & other
packages from .lake/packages/*/.lake/build), PID, start/end/elapsed, rc, parsed error count, fresh
nonempty object SHA-256, peak RSS of the child tree (os.wait4 ru_maxrss; /usr/bin/time absent).
Usage: python3 -I chk.py <rel-module-without-.lean> [--pfr] [--log <path>]
Exit status = checker rc, or 1 if the object is not fresh/nonempty."""
import os, sys, json, time, hashlib, re, subprocess, datetime
CLONE = '/workspace/cp2/src'; TREE = CLONE + '/.lake/cleanup-part2-oleans'
RUNTIME = CLONE + '/.lake/cleanup-part2-pfr-runtime'; EV = '/workspace/cp2/evidence/logs'
ORDINARY_PATH = os.path.expanduser('~/.elan/bin') + ':/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin'
args = sys.argv[1:]; pfr = '--pfr' in args; args = [a for a in args if a != '--pfr']
log = None
if '--log' in args:
    i = args.index('--log'); log = args[i + 1]; del args[i:i + 2]
rel = args[0]
PHASE = os.environ.get('CHK_PHASE', 'misc')
log = log or f'{EV}/{PHASE}/modules/{rel}.log'
os.makedirs(os.path.dirname(log), exist_ok=True)
def sha(p):
    h = hashlib.sha256()
    with open(p, 'rb') as f:
        for b in iter(lambda: f.read(1 << 20), b''): h.update(b)
    return h.hexdigest()
src = f'{CLONE}/{rel}.lean'
env = dict(os.environ, TCSLIB_OLEANS=TREE, PATH=ORDINARY_PATH)
env.pop('LEAN_PATH', None); env.pop('PFR_BOOTSTRAP_CONFIG', None)
if pfr:
    env['PATH'] = RUNTIME + '/bin:' + ORDINARY_PATH
    env['PFR_BOOTSTRAP_CONFIG'] = RUNTIME + '/config.json'
pkgs = sorted(d for d in os.listdir(CLONE + '/.lake/packages'))
TOOLCHAIN_LIB = os.path.expanduser('~/.elan/toolchains/leanprover--lean4---v4.25.0/lib/lean')
def obj(mod):
    rp = mod.replace('.', '/') + '.olean'
    for base in [TREE] + [f'{CLONE}/.lake/packages/{p}/.lake/build/lib/lean' for p in pkgs] + [TOOLCHAIN_LIB]:
        if os.path.exists(f'{base}/{rp}'):
            q = f'{base}/{rp}'; return {'module': mod, 'object': q, 'sha256': sha(q), 'resolved': os.path.realpath(q)}
    return {'module': mod, 'object': None}
def header_imports(text):
    """Imports of the module header only: strip comments, then read `import` commands until the first
    other command (so docstring lines beginning with the word 'import' are never parsed)."""
    out = []; i = 0; n = len(text); depth = 0; buf = []
    while i < n:
        if text.startswith('/-', i): depth += 1; i += 2; continue
        if depth:
            if text.startswith('-/', i): depth -= 1; i += 2
            else: i += 1
            continue
        if text.startswith('--', i):
            j = text.find('\n', i); i = n if j < 0 else j; continue
        buf.append(text[i]); i += 1
    toks = ''.join(buf).split()
    k = 0
    while k < len(toks):
        if toks[k] in ('prelude', 'module'): k += 1; continue
        if toks[k] == 'public' and k + 1 < len(toks) and toks[k + 1] == 'import': k += 1; continue
        if toks[k] == 'import' and k + 1 < len(toks):
            out.append(toks[k + 1]); k += 2; continue
        break
    return out
imports = header_imports(open(src).read())
prereq = [obj(m) for m in imports]
missing = [p['module'] for p in prereq if p['object'] is None]
rec = {'module': rel, 'source': src, 'source_sha256': sha(src), 'tree': TREE, 'cwd': CLONE,
       'path_mode': 'PFR-adapter (31 PFR checks only)' if pfr else 'ordinary',
       'PATH': env['PATH'], 'command': f'bash scripts/lean_check_tree.sh {rel}',
       'direct_prerequisites': prereq}
ol = f'{TREE}/{rel}.olean'
with open(log, 'w') as h:
    if missing:
        rec.update(rc=None, status='SKIPPED_MISSING_PREREQUISITES', missing=missing)
        h.write('SKIPPED: missing prerequisites ' + ' '.join(missing) + '\n')
        print(json.dumps({k: rec[k] for k in ('module', 'status', 'missing')}))
        open(f'{EV}/checks-{PHASE}.jsonl', 'a').write(json.dumps(rec) + '\n'); sys.exit(2)
    t0 = time.time(); start = datetime.datetime.now(datetime.timezone.utc).isoformat()
    h.write(f'START {start}\nCMD {rec["command"]}\nCWD {CLONE}\nTCSLIB_OLEANS {TREE}\nPATH {env["PATH"]}\n'
            f'SOURCE {src} sha256={rec["source_sha256"]}\n'); h.flush()
    p = subprocess.Popen(['bash', 'scripts/lean_check_tree.sh', rel], cwd=CLONE, env=env, stdout=h, stderr=subprocess.STDOUT)
    _, status, ru = os.wait4(p.pid, 0)
    rc = os.waitstatus_to_exitcode(status)
    end = datetime.datetime.now(datetime.timezone.utc).isoformat()
    h.write(f'\nEND {end} RC {rc} elapsed={time.time()-t0:.1f}s pid={p.pid} maxrss={ru.ru_maxrss}KiB\n')
text = open(log).read()
errs = len(re.findall(r'(?m)^\S.*:\d+:\d+: error', text)) + len(re.findall(r'(?m)^error:', text))
fresh = os.path.exists(ol) and os.path.getsize(ol) > 0 and os.path.getmtime(ol) >= t0
rec.update(start=start, end=end, elapsed_s=round(time.time() - t0, 1), pid=p.pid, rc=rc,
           parsed_errors=errs, maxrss_kib=ru.ru_maxrss, object=ol, object_fresh_nonempty=fresh,
           object_sha256=sha(ol) if fresh else None,
           status='PASS' if rc == 0 and errs == 0 and fresh else 'FAIL', log=log)
open(f'{EV}/checks-{PHASE}.jsonl', 'a').write(json.dumps(rec) + '\n')
print(f"{rec['status']} {rel} rc={rc} errors={errs} fresh={fresh} {rec['elapsed_s']}s {ru.ru_maxrss//1024}MiB", flush=True)
sys.exit(0 if rec['status'] == 'PASS' else (rc or 1))
