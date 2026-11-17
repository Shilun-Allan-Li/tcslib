"""downorder.py <repo> <rev> <parent-rev> <outdir>: build inputs for a landing review.
changed.txt  = TCSlib/audits .lean modules added or modified between <parent-rev> and <rev>;
down.txt     = every module (TCSlib/** incl. root TCSlib, audits/**) that transitively imports a
               changed module (changed ones included);
order.txt    = upstream closure of down.txt in imports-first DFS order (ordergen's traversal);
order-noroot.txt = the same closure computed without the root `TCSlib` (fillinputs convention);
roots.txt    = Mathlib modules imported directly by order.txt."""
import sys, re, subprocess, os
repo, rev, prev, outd = sys.argv[1:5]
os.makedirs(outd, exist_ok=True)
git = lambda *a: subprocess.run(['git', '-C', repo, *a], capture_output=True, text=True, check=True).stdout
files = [f[:-5] for f in git('ls-tree', '-r', '--name-only', rev, 'TCSlib', 'TCSlib.lean', 'audits').split() if f.endswith('.lean')]
cache = {}
def imps(m):
    if m not in cache:
        s = git('show', f'{rev}:{m}.lean')
        cache[m] = re.findall(r'^import\s+(\S+)', s, re.M)
    return cache[m]
local = lambda n: n.split('.')[0] in ('TCSlib', 'audits')
rdep = {}
for m in files:
    for i in imps(m):
        if local(i): rdep.setdefault(i.replace('.', '/'), set()).add(m)
ch = [l.split('\t')[-1][:-5] for l in git('diff', '--name-status', '--diff-filter=AMR', prev, rev, '--', 'TCSlib', 'TCSlib.lean', 'audits').splitlines() if l.endswith('.lean')]
down, todo = set(), list(ch)
while todo:
    m = todo.pop()
    if m in down: continue
    down.add(m); todo.extend(rdep.get(m, ()))
def closure(roots):
    order, seen, mroots = [], set(), set()
    sys.setrecursionlimit(100000)
    def visit(m):
        if m in seen: return
        seen.add(m)
        for i in imps(m):
            if local(i): visit(i.replace('.', '/'))
            elif i.startswith('Mathlib'): mroots.add(i)
        order.append(m)
    for r in sorted(roots): visit(r)
    return order, mroots
order, mroots = closure(down)
order2, _ = closure(down - {'TCSlib'})
w = lambda n, xs: open(os.path.join(outd, n), 'w').write(''.join(x + '\n' for x in xs))
w('changed.txt', sorted(ch)); w('down.txt', sorted(down)); w('order.txt', order); w('order-noroot.txt', order2); w('roots.txt', sorted(mroots))
print(f'files {len(files)} changed {len(ch)} down {len(down)} order {len(order)} order-noroot {len(order2)} mathlib-roots {len(mroots)}')
