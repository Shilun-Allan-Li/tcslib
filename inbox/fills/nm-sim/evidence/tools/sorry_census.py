#!/usr/bin/env python3
"""`sorry` census of the final sweep (one log per module in logs/sweep/), against base-sorries.txt."""
import re, os
F = '/workspace/sim'; E = '/workspace/simpay/evidence'
order = [l.strip() for l in open(E + '/sweep-order.txt') if l.strip()]
found = {}
for m in order:
    lg = E + '/logs/sweep/' + m.replace('/', '.') + '.log'
    for l in open(lg):
        mm = re.match(r"(\S+\.lean):(\d+):(\d+): warning: declaration uses 'sorry'", l)
        if mm:
            path, ln, col = mm.group(1), int(mm.group(2)), int(mm.group(3))
            line = open(F + '/' + path).read().splitlines()[ln - 1]
            tok = re.match(r"[\w.'₀-₉!?]+", line[col:])
            found.setdefault(m, []).append(tok.group(0) if tok else f'?{ln}:{col}')
def short(m):
    return m[len('TCSlib/Complexity/'):] if m.startswith('TCSlib/Complexity/') else m
base = {}
for l in open(E + '/inputs/base-sorries.txt'):
    if l.startswith('TOTAL'): continue
    mod, cnt, names = [x.strip() for x in l.split(':', 2)]
    base[mod] = sorted(n.strip() for n in names.split(','))
now = {short(m): sorted(v) for m, v in found.items()}
out = []
for m in sorted(set(base) | set(now)):
    b, n = base.get(m, []), now.get(m, [])
    out.append(f"{m}: {len(n)}: {', '.join(n)}" + ('' if b == n else f"   [base {len(b)}: {', '.join(b)}]"))
out.append(f"TOTAL {sum(len(v) for v in now.values())} (base {sum(len(v) for v in base.values())})")
bs = set((m, x) for m in base for x in base[m]); ns = set((m, x) for m in now for x in now[m])
out.append(f"removed vs base: {sorted(bs - ns)}")
out.append(f"added vs base: {sorted(ns - bs)}")
print('\n'.join(out))
