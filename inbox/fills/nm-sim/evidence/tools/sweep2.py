#!/usr/bin/env python3
"""Resumable sweep: check the modules of sweep-order.txt in order, one per lean_check_tree call,
until about 270 s have passed; append to sweep.tsv; stop at the first failure."""
import subprocess, time, os, sys
E = '/workspace/simpay/evidence'; LG = E + '/logs/sweep'
os.makedirs(LG, exist_ok=True)
order = [l.strip() for l in open(E + '/sweep-order.txt') if l.strip()]
tsv = E + '/logs/sweep.tsv'
done = set()
if os.path.exists(tsv):
    for l in open(tsv):
        p = l.rstrip('\n').split('\t')
        if len(p) >= 2 and p[1] == '0': done.add(p[0])
        elif len(p) >= 2: print('FAILED earlier:', p[0]); sys.exit(1)
t0 = time.time()
for m in order:
    if m in done: continue
    if time.time() - t0 > 240: print('PAUSE', len(done), '/', len(order)); sys.exit(0)
    lg = LG + '/' + m.replace('/', '.') + '.log'
    with open(lg, 'w') as f:
        st = subprocess.run(['python3', '/workspace/simtools/chk.py', m], cwd='/workspace/sim',
                            stdout=f, stderr=subprocess.STDOUT).returncode
    last = open(lg).read().strip().splitlines()[-1]
    open(tsv, 'a').write(f'{m}\t{st}\t{last}\n')
    if st != 0: print('FAIL', m); sys.exit(1)
    done.add(m)
print('DONE', len(done), '/', len(order))
