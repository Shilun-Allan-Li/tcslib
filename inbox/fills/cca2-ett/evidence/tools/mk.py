#!/usr/bin/env python3
"""Make-like rebuild: for each target module, rebuild (in order.txt order, one module at a time
through scripts/lean_check_tree.sh) every module of its TCSlib import closure whose olean is older
than its source or than the olean of one of its imports. Usage: mk.py <log> <target>..."""
import os,sys,subprocess
ROOT='/workspace/ett'; OL=ROOT+'/.lake/tcslib-check-oleans'
order=[l.strip() for l in open('/workspace/ett-work/order-current.txt') if l.strip()]
pos={m:i for i,m in enumerate(order)}
def imps(m):
    p=f'{ROOT}/{m}.lean'
    return [l.split()[1].replace('.','/') for l in open(p) if l.startswith('import TCSlib')]
def closure(ts):
    seen=set(); st=list(ts)
    while st:
        x=st.pop()
        if x in seen: continue
        seen.add(x); st+= imps(x)
    return seen
log=sys.argv[1]; targets=sys.argv[2:]
cl=closure(targets)
for m in cl:
    if m not in pos: print('NOT IN ORDER',m); sys.exit(2)
def mt(p): return os.path.getmtime(p) if os.path.exists(p) else -1
for m in sorted(cl,key=lambda x:pos[x]):
    o=f'{OL}/{m}.olean'
    stale = mt(o) < mt(f'{ROOT}/{m}.lean') or any(mt(o) < mt(f'{OL}/{d}.olean') for d in imps(m))
    if stale:
        r=subprocess.run(['/workspace/ett-tools/check.sh',m,log])
        with open(log) as f: last=f.read().strip().split('\n')[-1]
        print(m, last.split()[-1])
        if 'status=0' not in last: sys.exit(1)
