#!/usr/bin/env python3
"""Print the sealed working-tree probe errors of one module (latest sealwt run) with the source
line and the goal (⊢ part) of each error. python3 -I errs.py <module path> [maxlines]"""
import sys, re
path = sys.argv[1]; mx = int(sys.argv[2]) if len(sys.argv) > 2 else 14
CLONE = '/workspace/cp2/src'
rel = f'.lake/cleanup-part2-probes/seal/wt/{path}'
log = open(f'/workspace/cp2/evidence/logs/seal-wt/modules/{rel}.log').read()
probe = open(f'{CLONE}/{rel}.lean').read().split('\n')
w = next(i for i, l in enumerate(probe) if l.startswith('-- CP2 WHOLE-FILE SEAL')) + 1
b = next(i for i, l in enumerate(probe) if l == '-- CP2 END SEAL') + 1
off = b - w + 2
src = open(f'{CLONE}/{path}.lean').read().split('\n')
parts = re.split(r'(?m)^(?=\S*\.lean:\d+:\d+: )', log)
for p in parts:
    m = re.match(r'\S*\.lean:(\d+):(\d+): error[^:]*: ?', p)
    if not m: continue
    s = int(m.group(1)) - off
    body = p[m.end():].split('CP2-EOF')[0].rstrip().split('\n')
    print(f'=== {s}:{m.group(2)}  > {src[s-1].strip()[:150]}')
    head = body[:6]
    gi = [i for i, l in enumerate(body) if l.startswith('⊢')]
    print('\n'.join('   ' + x[:220] for x in head))
    if gi and gi[0] >= 6:
        print('   ...'); print('\n'.join('   ' + x[:220] for x in body[gi[0]:gi[0] + mx]))
