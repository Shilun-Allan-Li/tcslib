import sys, re, os
# usage: closurecheck.py <worktree> <target module> <out file>
# Concatenate exactly the target's import closure within TCSlib.Programs, in dependency order, importing
# only the external modules that the closure itself imports, so the environment matches a real build.
wt, target, out = sys.argv[1], sys.argv[2], sys.argv[3]
def path(m): return f'{wt}/{m.replace(".", "/")}.lean'
def parse(m):
    own, ext = [], []
    for l in open(path(m), encoding='utf-8').read().split('\n'):
        mi = re.match(r'^import (\S+)\s*$', l)
        if mi:
            (own if mi.group(1).startswith('TCSlib.Programs') else ext).append(mi.group(1))
    return own, ext
order, seen = [], set()
def visit(m):
    if m in seen: return
    seen.add(m)
    for d in parse(m)[0]: visit(d)
    order.append(m)
visit(target)
imps = []
for m in order:
    for e in parse(m)[1]:
        if e not in imps: imps.append(e)
parts = []
for m in order:
    body = [l for l in open(path(m), encoding='utf-8').read().split('\n') if not re.match(r'^import \S+\s*$', l)]
    tag = 'CC_' + m.replace('.', '_')
    parts.append(f'\n-- ===== {m} =====\nsection {tag}\n' + '\n'.join(body) + f'\nend {tag}\n')
open(out, 'w', encoding='utf-8').write('\n'.join(f'import {i}' for i in imps) + '\n' + ''.join(parts))
print(len(order))
