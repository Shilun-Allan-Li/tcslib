#!/usr/bin/env python3
"""Print the sealed-probe errors of one module with source line numbers (cleanup-part2 J work).

python3 -I sealdiag.py <phase> <module path without .lean> [--src <source file>] [--max N]
Maps probe lines back to source lines by removing the inserted seal block and shows each error
message in full together with its source line."""
import sys, json, re
phase, path = sys.argv[1], sys.argv[2]
src = None; mx = 400
if '--src' in sys.argv: src = sys.argv[sys.argv.index('--src') + 1]
if '--max' in sys.argv: mx = int(sys.argv[sys.argv.index('--max') + 1])
EV = '/workspace/cp2/evidence/logs'
d = json.load(open(f'{EV}/seal-{phase}.json'))[path]
rel = f'.lake/cleanup-part2-probes/seal/{phase}/{path}'
probe = open(f'/workspace/cp2/src/{rel}.lean').read().split('\n')
w = next(i for i, l in enumerate(probe) if l.startswith('-- CP2 WHOLE-FILE SEAL')) + 1
b = next(i for i, l in enumerate(probe) if l == '-- CP2 END SEAL') + 1
off = b - w + 2
log = open(f'{EV}/seal-{phase}/modules/{rel}.log').read()
srcl = open(src).read().split('\n') if src else None
parts = re.split(r'(?m)^(?=\S*\.lean:\d+:\d+: )', log)
n = 0
for p in parts:
    m = re.match(r'\S*\.lean:(\d+):(\d+): (error|warning)[^:]*: ?', p)
    if not m or m.group(3) != 'error': continue
    ln = int(m.group(1)); s = ln - off if ln > b else ln
    body = p[m.end():].split('CP2-EOF')[0].rstrip()
    decl = max((f for f in d['diagnostics'] if f['error_line'] == ln), key=lambda f: 0, default={'decl': '?'})['decl']
    print(f'=== src {s}:{m.group(2)} [{decl}]')
    if srcl: print('  > ' + srcl[s - 1])
    print('\n'.join('  ' + x for x in body.split('\n')[:40]))
    n += 1
    if n >= mx: break
print(f'-- {n} errors; failing: {d["failing_declarations"]}')
