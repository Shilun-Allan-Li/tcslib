import sys, os, re
root = sys.argv[1]
starts = sys.argv[2:]
seen = set(); order = []
def path(m): return os.path.join(root, m.replace('.', '/') + '.lean')
def visit(m):
    if m in seen: return
    seen.add(m)
    p = path(m)
    if not os.path.exists(p): return
    for line in open(p, encoding='utf-8'):
        mm = re.match(r'^import\s+(\S+)', line)
        if mm and mm.group(1).startswith('TCSlib'):
            visit(mm.group(1))
    order.append(m)
for s in starts: visit(s)
for m in order: print(m)
