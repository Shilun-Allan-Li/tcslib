"""chain.py <worktree> <changed module path>...: the modules a pre-replay compile check needs,
in dependency order: the changed modules and every module on an import path between two of them
(downstream of one changed module and upstream of another). Paths are without `.lean`, as in
the bootstrap's order list. The root `TCSlib` is never listed."""
import os
import re
import sys

wt, changed = sys.argv[1], sys.argv[2:]
imp = {}


def imports(m):
    if m not in imp:
        p = os.path.join(wt, m + '.lean')
        if not os.path.exists(p):
            sys.exit(f'missing module {m}')
        imp[m] = [i.replace('.', '/') for i in
                  re.findall(r'^import\s+(TCSlib\S*)', open(p, encoding='utf-8').read(), re.M)
                  if i != 'TCSlib']
    return imp[m]


order, state = [], {}


def visit(m):
    if state.get(m) == 2:
        return
    if state.get(m) == 1:
        sys.exit(f'import cycle at {m}')
    state[m] = 1
    for i in imports(m):
        visit(i)
    state[m] = 2
    order.append(m)


sys.setrecursionlimit(20000)
for m in changed:
    visit(m)
up = set(order)                       # the changed modules' upstream closure (themselves included)
reaches = {m: (m in changed) for m in order}
for m in order:                       # topological: imports come first
    if any(reaches[i] for i in imports(m) if i in reaches):
        reaches[m] = True             # downstream of some changed module
print('\n'.join(m for m in order if m in up and reaches[m]))
