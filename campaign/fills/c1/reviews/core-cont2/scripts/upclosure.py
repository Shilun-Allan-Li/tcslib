import sys, os, re
# usage: upclosure.py <worktree> <module path without .lean, e.g. TCSlib/Complexity/TuringMachine/NDCodeSimulator>
# Prints the TCSlib upstream import closure (excluding the module itself), one module per line, sorted.
wt, root = sys.argv[1], sys.argv[2]
def imports(mod):
    p = os.path.join(wt, mod + '.lean')
    out = []
    for l in open(p, encoding='utf-8'):
        m = re.match(r'^import\s+(TCSlib\S*)', l)
        if m: out.append(m.group(1).replace('.', '/'))
        elif l.strip() and not l.startswith('import') and not l.startswith('/-') and not l.startswith('--') and not l.startswith(' ') and not l.startswith('Copyright') and not l.startswith('Released') and not l.startswith('Authors') and not l.startswith('-/'):
            pass
    return out
seen, stack = set(), [root]
while stack:
    m = stack.pop()
    for d in imports(m):
        if d not in seen: seen.add(d); stack.append(d)
for m in sorted(seen): print(m)
