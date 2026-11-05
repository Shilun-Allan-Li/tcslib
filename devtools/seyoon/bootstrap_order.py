"""bootstrap_order.py <worktree>: every module the root `TCSlib.lean` imports, transitively (what CI
builds), without the root itself, as paths without `.lean`, in dependency order (imports first).
Replay lists reach outside `TCSlib/Complexity` (its importers in other folders), so a snapshot needs
them all. A missing import or a cycle stops it (exit 2)."""
import os, re, sys
wt = sys.argv[1]
def imports(m):
    p = os.path.join(wt, m + '.lean')
    if not os.path.exists(p): sys.exit(f'missing module {m}')
    return [i.replace('.', '/') for i in re.findall(r'^import\s+(TCSlib\S*)', open(p).read(), re.M)]
roots = imports('TCSlib')
order, state = [], {}
def visit(m):
    if state.get(m) == 2: return
    if state.get(m) == 1: sys.exit(f'import cycle at {m}')
    state[m] = 1
    for i in imports(m):
        if i != 'TCSlib': visit(i)
    state[m] = 2; order.append(m)
sys.setrecursionlimit(20000)
for m in sorted(roots): visit(m)
print('\n'.join(order))
