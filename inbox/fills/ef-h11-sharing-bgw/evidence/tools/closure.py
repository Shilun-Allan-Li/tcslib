import sys, os, re
root = sys.argv[1]; mods = sys.argv[2:]
seen = set(); order = []
def imports(m):
    p = os.path.join(root, m.replace('.', '/') + '.lean')
    out = []
    for line in open(p):
        mm = re.match(r'^import\s+(\S+)', line)
        if mm: out.append(mm.group(1))
    return out
def visit(m):
    if m in seen: return
    seen.add(m)
    if not m.startswith('TCSlib'): return
    for i in imports(m): visit(i)
    order.append(m)
for m in mods: visit(m)
for m in order: print(m.replace('.', '/'))
