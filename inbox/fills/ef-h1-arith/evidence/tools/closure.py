import sys, os, re
root = sys.argv[1]; mods = sys.argv[2:]
seen = {}; order = []; mathlib = set()
def imports(m):
    p = os.path.join(root, m.replace('.', '/') + '.lean')
    out = []
    for line in open(p, encoding='utf-8'):
        mm = re.match(r'^import\s+(\S+)', line)
        if mm: out.append(mm.group(1))
    return out
def visit(m):
    if m in seen: return
    seen[m] = 1
    for i in imports(m):
        if i.startswith('TCSlib'): visit(i)
        else: mathlib.add(i)
    order.append(m)
for m in mods: visit(m)
with open(os.environ.get('ORDER_OUT', '/dev/stdout'), 'w') as f:
    for m in order: f.write(m.replace('.', '/') + '\n')
with open(os.environ.get('ROOTS_OUT', '/dev/null'), 'w') as f:
    for m in sorted(mathlib): f.write(m + '\n')
print(len(order), len(mathlib), file=sys.stderr)
