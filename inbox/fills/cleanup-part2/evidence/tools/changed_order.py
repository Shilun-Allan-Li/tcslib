#!/usr/bin/env python3
"""Changed modules (working tree vs a revision) in current topological order.
python3 -I changed_order.py <rev> <out.txt>"""
import sys, subprocess
ROOT = '/workspace/cp2/src'
rev, out = sys.argv[1], sys.argv[2]
subprocess.run(['python3', '-I', '/workspace/cp2/tools/order.py', '/tmp/order-cur.txt'], check=True, capture_output=True)
order = [l.strip() for l in open('/tmp/order-cur.txt') if l.strip()]
changed = {p[:-5] for p in subprocess.check_output(['git', '-C', ROOT, 'diff', '--name-only', rev], text=True).split() if p.endswith('.lean')}
sel = [m for m in order if m in changed]
open(out, 'w').write('\n'.join(sel) + '\n')
print(len(changed), 'changed;', len(sel), 'ordered')
