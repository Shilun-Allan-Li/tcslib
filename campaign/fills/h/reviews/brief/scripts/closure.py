# Import closure of TCSlib modules within a worktree. Usage: closure.py <worktree> <Module.Name> [...]
import sys, os, re
root = sys.argv[1]
seen = {}
def deps(mod):
    p = os.path.join(root, *mod.split('.')) + '.lean'
    if not os.path.exists(p):
        return None
    out = []
    for line in open(p, encoding='utf-8'):
        m = re.match(r'^import\s+(\S+)', line)
        if m:
            out.append(m.group(1))
        elif line.strip() and not line.startswith('import') and not line.startswith('--') and not line.startswith('/-') and not line.startswith('Copyright') and not line.startswith('Released') and not line.startswith('Authors') and not line.startswith('-/'):
            break
    return out
stack = list(sys.argv[2:])
order = []
def visit(m):
    if m in seen: return
    seen[m] = True
    d = deps(m)
    if d is None: return
    for x in d:
        if x.startswith('TCSlib'): visit(x)
    order.append(m)
for m in stack: visit(m)
for m in order: print(m)
