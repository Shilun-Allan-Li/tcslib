#!/usr/bin/env python3
"""Affected replay order: every TCSlib module whose source changed since the ancestor, and every
module importing one of them (transitively, current source imports), in the current topological
order (tools/order.py). python3 -I affected.py <order.txt> <out.txt>"""
import sys, subprocess
ROOT = '/workspace/cp2/src'
src = open('/workspace/cp2/tools/chk.py').read()
exec(src.split('def header_imports')[1].split('imports = header_imports')[0].join(['def header_imports', '']))
order = [l.strip() for l in open(sys.argv[1]) if l.strip()]
changed = {p[:-5] for p in subprocess.check_output(['git', '-C', ROOT, 'diff', '--name-only', '1aa5506f58f77c215e56d24311ec33bd931cacf1', 'HEAD'], text=True).split() if p.endswith('.lean')}
aff = set(changed)
for m in order:
    imps = [x.replace('.', '/') for x in header_imports(open(f'{ROOT}/{m}.lean').read()) if x.startswith('TCSlib')]
    if any(i in aff for i in imps): aff.add(m)
sel = [m for m in order if m in aff]
open(sys.argv[2], 'w').write('\n'.join(sel) + '\n')
print(len(changed), 'changed;', len(sel), 'affected (incl. changed) of', len(order))
