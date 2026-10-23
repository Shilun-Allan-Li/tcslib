#!/usr/bin/env python3
"""usage: inline.py <worktree> <out> <module path>... -- <lean tail file>
Concatenate the given modules (in order) into one file: imports hoisted and deduplicated, imports
of the inlined modules dropped, each body wrapped in its own `section` ... `end`; then the tail.
The caller checks that no remaining import is downstream of an inlined module."""
import os, sys
args = sys.argv[1:]
wt, out = args[0], args[1]
k = args.index('--')
mods, tailf = args[2:k], args[k + 1]
names = {'import ' + m.replace('/', '.') for m in mods}
imps, bodies = [], []
for m in mods:
    L = open(os.path.join(wt, m + '.lean'), encoding='utf-8').read().rstrip('\n').split('\n')
    last = max(i for i, l in enumerate(L) if l.startswith('import '))
    pre = []
    for l in L[:last + 1]:
        if l.startswith('import '):
            if l not in names and l not in imps:
                imps.append(l)
        else:
            pre.append(l)  # header comments before or between imports: kept in the body
    assert not any(l.lstrip().startswith('import ') for l in L[last + 1:])
    bodies.append(f'\n-- inlined module: {m}\n' + '\n'.join(pre) + '\nsection\n' + '\n'.join(L[last + 1:]) + '\nend\n')
tail = open(tailf, encoding='utf-8').read()
open(out, 'w', encoding='utf-8').write('\n'.join(imps) + '\nimport Lean.Util.FoldConsts\n' + ''.join(bodies) + tail)
print('imports', len(imps), 'modules', len(mods))
