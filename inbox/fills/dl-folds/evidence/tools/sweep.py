#!/usr/bin/env python3
"""Resumable sweep: check the modules of an order list in order, one per lean_check_tree call,
until about 240 s have passed; append to <tsv>; stop at the first failure.
usage: sweep.py ORDER TSV LOGDIR"""
import subprocess, time, os, sys
order_f, tsv, LG = sys.argv[1], sys.argv[2], sys.argv[3]
os.makedirs(LG, exist_ok=True)
order = [l.strip() for l in open(order_f) if l.strip()]
done = set()
if os.path.exists(tsv):
    for l in open(tsv):
        p = l.rstrip('\n').split('\t')
        if len(p) >= 2 and p[1] == '0': done.add(p[0])
        elif len(p) >= 2: print('FAILED earlier:', p[0]); sys.exit(1)
import re
est = {}
bt = '/workspace/foldpay/evidence/logs/bootstrap.tsv'
if os.path.exists(bt):
    for l in open(bt):
        p = l.rstrip('\n').split('\t')
        mm = re.search(r'wall=([0-9.]+)s', l)
        if mm: est[p[0]] = float(mm.group(1))
t0 = time.time()
for m in order:
    if m in done: continue
    if time.time() - t0 + est.get(m, 60) * 1.2 + 5 > 285:
        print('PAUSE', len(done), '/', len(set(order))); sys.exit(0)
    lg = LG + '/' + m.replace('/', '.') + '.log'
    with open(lg, 'w') as f:
        st = subprocess.run(['python3', '/workspace/foldtools/chk.py', m], cwd='/workspace/folds',
                            stdout=f, stderr=subprocess.STDOUT).returncode
    last = open(lg).read().strip().splitlines()[-1]
    open(tsv, 'a').write(f'{m}\t{st}\t{last}\n')
    if st != 0: print('FAIL', m); sys.exit(1)
    done.add(m)
print('DONE', len(done), '/', len(set(order)))
