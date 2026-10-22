#!/usr/bin/env python3
"""usage: append_probe.py <module> <out> <probe files...>
The module, with each probe's imports merged into its import block (deduplicated, none of them may
be the module itself or downstream of it: the caller checks), and each probe's body (imports
removed) appended after the module's last line."""
import sys
mod, out, probes = sys.argv[1], sys.argv[2], sys.argv[3:]
L = open(mod, encoding='utf-8').read().rstrip('\n').split('\n')
last_import = max(i for i, l in enumerate(L) if l.startswith('import '))
imps = set(l for l in L[:last_import + 1] if l.startswith('import '))
extra, bodies = [], []
for p in probes:
    P = open(p, encoding='utf-8').read().split('\n')
    for l in P:
        if l.startswith('import ') and l not in imps and l != 'import TCSlib.Complexity.TuringMachine.CodeSimulator':
            imps.add(l); extra.append(l)
    bodies.append('\n-- appended probe: ' + p.split('/')[-1] + '\n' + '\n'.join(l for l in P if not l.startswith('import ')).rstrip('\n'))
T = L[:last_import + 1] + extra + L[last_import + 1:]
open(out, 'w', encoding='utf-8').write('\n'.join(T) + '\n' + '\n'.join(bodies) + '\n')
print('extra imports:', extra, '| line shift', len(extra))
