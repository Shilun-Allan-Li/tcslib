"""pins.py (gsw-6a-fills staging, issued-fills-r1: copied from the bb1-sim pack's tools/ unchanged
except this first docstring line; CHANGED = the six unit files, DELTA = records pin vs base)
pins.py <graphdir> <changedfile> <deltafile> <outdir> (bb1-sim fill staging, issued-fill-r1; adapted from the cs1
staging tool plan2.py: same order/roots/SOURCE/base-sorries rules; closures.txt gains a header for this job and an
INFO-DELTA section). DOWN: modules downstream of a CHANGED module (CHANGED included), root `TCSlib` excluded.
ORDER: upstream closure of DOWN in the full DFS post-order (imports in file order; audits/*/Checks visited after the
root). roots: Mathlib modules ORDER imports directly. SOURCE: sha256 lines for ORDER. base-sorries: the graph's
syntactic scan (comments and strings stripped) restricted to ORDER."""
import sys, json, os
gd, chf, delf, outd = sys.argv[1:5]
changed = open(chf).read().split(); delta = open(delf).read().split()
g = json.load(open(gd+'/mods.json')); imps, ml = g['imports'], g['mathlib']
full = open(gd+'/order-full.txt').read().split(); pos = {m:i for i,m in enumerate(full)}
rev = {}
for m, xs in imps.items():
    for x in xs: rev.setdefault(x, []).append(m)
def clo(st, e):
    seen=set(); st=list(st)
    while st:
        x=st.pop()
        if x in seen: continue
        seen.add(x); st.extend(e.get(x, []))
    return seen
downall = clo(changed, rev)
down = {m for m in downall if m in pos and m != 'TCSlib'}
order = sorted({m for m in clo(down, imps) if m in pos}, key=pos.get)
os.makedirs(outd, exist_ok=True)
open(outd+'/order.txt','w').write('\n'.join(order)+'\n')
open(outd+'/roots.txt','w').write('\n'.join(sorted({x for m in order for x in ml[m]}))+'\n')
src = {l.split()[1][:-5]: l for l in open(gd+'/SOURCE-full.txt')}
open(outd+'/SOURCE-SHA256SUMS','w').write(''.join(src[m] for m in order))
so = [l for l in open(gd+'/sorries.txt') if not l.startswith('TOTAL') and l.split(':')[0] in set(order)]
tot = sum(int(l.split(':')[1]) for l in so)
open(outd+'/base-sorries.txt','w').write(''.join(so)+f'TOTAL {tot}\n')
opos = {m:i+1 for i,m in enumerate(order)}
hdr = open(outd+'/closures.header').read()
with open(outd+'/closures.txt','w') as f:
    f.write(hdr)
    for m in sorted(changed, key=pos.get): f.write(f'CHANGED\t{opos[m]}\t{pos[m]+1}\t{m}\n')
    for m in sorted(down, key=pos.get): f.write(f'DOWN\t{opos[m]}\t{pos[m]+1}\t{m}\n')
    for m in sorted(delta, key=pos.get): f.write(f'INFO-DELTA\t{opos.get(m,"-")}\t{pos[m]+1}\t{m}\n')
print('changed',len(changed),'down',len(down),'down-with-root-and-audits',sorted(x for x in downall if x not in down),
      'order',len(order),'full',len(full),'roots',len({x for m in order for x in ml[m]}),'sorry decls',tot,'in',len(so),'modules')
