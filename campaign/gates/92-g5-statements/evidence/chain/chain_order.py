"""Order for compiling a change into a snapshot clone.
Usage: python3 -I chain_order.py <worktree> <changed modules, comma-separated> <targets, comma-separated>
Prints, in dependency order, every module in the upstream closure of the targets (targets included)
that imports a changed module transitively or is one."""
import os, re, sys
wt = sys.argv[1]; changed = set(sys.argv[2].split(',')); targets = sys.argv[3].split(',')
def imps(m):
    f = os.path.join(wt, m.replace('.', '/') + '.lean')
    return [x for x in re.findall(r'^import\s+(\S+)', open(f).read(), re.M) if x.startswith('TCSlib')] if os.path.exists(f) else []
up = set(targets); st = list(targets)
while st:
    x = st.pop()
    for y in imps(x):
        if y not in up: up.add(y); st.append(y)
memo = {}
def reaches(m):
    if m in changed: return True
    if m not in memo: memo[m] = False; memo[m] = any(reaches(y) for y in imps(m))
    return memo[m]
need = {m for m in up if reaches(m)}
order, seen = [], set()
def visit(m):
    if m in seen: return
    seen.add(m)
    for y in imps(m):
        if y in need: visit(y)
    order.append(m)
for m in sorted(need): visit(m)
print('\n'.join(order))
