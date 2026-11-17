"""plan6b.py (gsw-6b-statements staging, issued-6b-r1; adapted from issued-fills-r1/tools/pins.py, itself
the bb1-sim pack's): <graphdir> <changedfile> <importsfile> <outdir>, from graph.py's output on the synthetic base tree.
ORDER: the modules reachable from the root `TCSlib` in graph.py's DFS post-order (imports in file order), root last;
the audits/*/Checks roots are left out (neither is downstream of a CHANGED module; checked and printed).
CHANGED: the existing Lean files the job may edit. DOWN: modules downstream of a CHANGED module, CHANGED included,
root excluded (the sweep). IMPORTS: existing modules the new 6b files are expected to import (r3 sketches).
PREFIX: the upstream closure of IMPORTS and DOWN in ORDER order, the bootstrap needed before the new modules.
Writes order.txt, roots.txt (Mathlib modules ORDER imports directly), prefix.txt, prefix-roots.txt,
SOURCE-SHA256SUMS (ORDER), base-sorries.txt (graph.py's syntactic scan restricted to ORDER) and closures.txt."""
import sys, json, os
gd, chf, imf, outd = sys.argv[1:5]
changed = open(chf).read().split(); wanted = open(imf).read().split()
g = json.load(open(gd + '/mods.json')); imps, ml = g['imports'], g['mathlib']
full = open(gd + '/order-full.txt').read().split()
order = full[:full.index('TCSlib') + 1]
pos = {m: i for i, m in enumerate(order)}
for m in changed + wanted:
    assert m in pos, m
rev = {}
for m, xs in imps.items():
    for x in xs: rev.setdefault(x, []).append(m)
def clo(st, e):
    seen = set(); st = list(st)
    while st:
        x = st.pop()
        if x in seen: continue
        seen.add(x); st.extend(e.get(x, []))
    return seen
downall = clo(changed, rev)
down = sorted((m for m in downall if m in pos and m != 'TCSlib'), key=pos.get)
outside = sorted(m for m in downall if m not in pos)
prefix = sorted(clo(down + wanted, imps) & set(pos), key=pos.get)
os.makedirs(outd, exist_ok=True)
w = lambda n, ls: open(os.path.join(outd, n), 'w').write(''.join(x + '\n' for x in ls))
w('order.txt', order)
w('roots.txt', sorted({x for m in order for x in ml[m]}))
w('prefix.txt', prefix)
w('prefix-roots.txt', sorted({x for m in prefix for x in ml[m]}))
src = {l.split()[1][:-5]: l for l in open(gd + '/SOURCE-full.txt')}
open(os.path.join(outd, 'SOURCE-SHA256SUMS'), 'w').write(''.join(src[m] for m in order))
so = [l for l in open(gd + '/sorries.txt') if not l.startswith('TOTAL') and l.split(':')[0] in pos]
tot = sum(int(l.split(':')[1]) for l in so)
open(os.path.join(outd, 'base-sorries.txt'), 'w').write(''.join(so) + f'TOTAL {tot}\n')
hdr = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'closures.header')).read()
with open(os.path.join(outd, 'closures.txt'), 'w') as f:
    f.write(hdr)
    for tag, ms in (('CHANGED', changed), ('DOWN', down), ('IMPORTS', wanted)):
        for m in sorted(ms, key=pos.get): f.write(f'{tag}\t{pos[m] + 1}\t{m}\n')
print('order', len(order), 'roots', len({x for m in order for x in ml[m]}), 'prefix', len(prefix),
      'prefix-roots', len({x for m in prefix for x in ml[m]}), 'changed', len(changed), 'down', len(down),
      'imports', len(wanted), 'downstream outside order', outside, 'sorry decls', tot, 'in', len(so), 'modules')
