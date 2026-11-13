#!/usr/bin/env python3
"""Explicit-unfold scan, step 2 (dl-folds): for each changed file, write its scan module with
rwids.py, compile it against the olean tree, and collect `file<TAB>id<TAB>constant<TAB>class<TAB>module`
rows. usage: rwids_run.py FILELIST OUTDIR"""
import os, re, subprocess, sys
F = '/workspace/folds'
files = [l.strip() for l in open(sys.argv[1]) if l.strip()]
out = sys.argv[2]
os.makedirs(out, exist_ok=True)
LP = F + '/.lake/tcslib-check-oleans:' + ':'.join(
    f'{F}/.lake/packages/{d}/.lake/build/lib/lean' for d in sorted(os.listdir(F + '/.lake/packages')))
env = dict(os.environ, LEAN_PATH=LP, PATH=os.path.expanduser('~/.elan/bin') + ':' + os.environ['PATH'])
tsv = open(f'{out}/rwids-final.tsv', 'a')
done = set()
if os.path.exists(f'{out}/done.txt'):
    done = set(open(f'{out}/done.txt').read().split())
for f in files:
    if f in done:
        continue
    key = f[len('TCSlib/Cryptography/'):-5].replace('/', '_')
    mod = f'scratch/rwids/Scan_{key}'
    subprocess.run(['python3', '/workspace/foldtools/rwids.py', F, f, mod], check=True,
                   capture_output=True)
    p = subprocess.run(['lean', mod + '.lean'], cwd=F, env=env, capture_output=True, text=True)
    log = p.stdout + p.stderr
    open(f'{out}/scan-{key}.log', 'w').write(log)
    if p.returncode != 0:
        print('SCAN FAILED', f)
        sys.exit(1)
    for l in log.splitlines():
        if re.match(r'^[^\t ]+\t[^\t]+\t[^\t]+\t[^\t]+$', l):
            tsv.write(f'{f}\t{l}\n')
    tsv.flush()
    open(f'{out}/done.txt', 'a').write(f + '\n')
    print('ok', f)
