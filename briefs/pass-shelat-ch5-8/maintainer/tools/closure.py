import sys, os, re
root = sys.argv[1]
def imports(mod):
    p = os.path.join(root, mod.replace('.', '/') + '.lean')
    if not os.path.exists(p): return []
    out = []
    for line in open(p, encoding='utf-8'):
        m = re.match(r'^import\s+(\S+)', line)
        if m: out.append(m.group(1))
    return out
def closure(mod):
    seen, st = set(), [mod]
    while st:
        x = st.pop()
        if x in seen: continue
        seen.add(x)
        st.extend(i for i in imports(x) if i.startswith('TCSlib'))
    return seen
for q in sys.argv[2:]:
    a, b = q.split(':')
    print(f"{a} imports {b}? {b in closure(a)}")
