#!/usr/bin/env python3
"""Like sealdiag.py, but drop diagnostics whose message mentions PolyExpr/`.eval` (standing-rule
notation, unsealed in the standard variant) and locate each source line in a newer source file by
exact text match. python3 -I sealdiag2.py <phase> <module> <base src> <head src>"""
import sys, json, re
phase, path, bsrc, hsrc = sys.argv[1:5]
EV = '/workspace/cp2/evidence/logs'
d = json.load(open(f'{EV}/seal-{phase}.json'))[path]
rel = f'.lake/cleanup-part2-probes/seal/{phase}/{path}'
probe = open(f'/workspace/cp2/src/{rel}.lean').read().split('\n')
w = next(i for i, l in enumerate(probe) if l.startswith('-- CP2 WHOLE-FILE SEAL')) + 1
b = next(i for i, l in enumerate(probe) if l == '-- CP2 END SEAL') + 1
off = b - w + 2
log = open(f'{EV}/seal-{phase}/modules/{rel}.log').read()
B = open(bsrc).read().split('\n'); H = open(hsrc).read().split('\n')
parts = re.split(r'(?m)^(?=\S*\.lean:\d+:\d+: )', log)
n = 0
for p in parts:
    m = re.match(r'\S*\.lean:(\d+):(\d+): error[^:]*: ?', p)
    if not m: continue
    body = p[m.end():].split('CP2-EOF')[0].rstrip()
    if 'PolyExpr' in body or '.eval' in body: continue
    s = int(m.group(1)) - off
    txt = B[s - 1] if 0 < s <= len(B) else ''
    hl = [i + 1 for i, l in enumerate(H) if l == txt]
    print(f'=== base {s}:{m.group(2)} head {hl[:3]}')
    print('  > ' + txt)
    print('\n'.join('  ' + x for x in body.split('\n')[:14]))
    n += 1
print(f'-- {n} non-notation errors')
