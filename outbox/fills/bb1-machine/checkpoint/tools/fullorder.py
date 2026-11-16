r"""fullorder.py <repo> <rev> <out> <root>... (int-331-tip, new): the local import closure of the roots at <rev>, imports-first
(DFS, downorder.py's parsing `^import\s+(\S+)`, local = TCSlib.* / audits.*; roots visited in sorted order, as downorder.closure)."""
import sys, re, subprocess
repo, rev, out = sys.argv[1:4]; roots = sys.argv[4:]
git = lambda *a: subprocess.run(['git', '-C', repo, *a], capture_output=True, text=True, check=True).stdout
local = lambda n: n.split('.')[0] in ('TCSlib', 'audits')
order, seen = [], set(); sys.setrecursionlimit(100000)
def visit(m):
    if m in seen: return
    seen.add(m)
    for i in re.findall(r'^import\s+(\S+)', git('show', f'{rev}:{m}.lean'), re.M):
        if local(i): visit(i.replace('.', '/'))
    order.append(m)
for r in sorted(roots): visit(r)
open(out, 'w').write(''.join(m + '\n' for m in order)); print(f'{rev[:8]} roots {sorted(roots)}: closure {len(order)}')
