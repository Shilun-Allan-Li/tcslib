import sys, os, re
root = sys.argv[1]
def path(m): return os.path.join(root, *m.split('.')) + '.lean'
def imports(m):
    p = path(m)
    if not os.path.exists(p): return None
    out = []
    for line in open(p, encoding='utf-8'):
        s = line.strip()
        if s.startswith('import '):
            out += s[len('import '):].split()
        elif s and not s.startswith('--') and not s.startswith('/-') and not s.startswith('import') and out:
            pass
    return out
def closure(m):
    seen = set(); stack = [m]; ext = set()
    while stack:
        x = stack.pop()
        if x in seen: continue
        seen.add(x)
        im = imports(x)
        if im is None: ext.add(x); continue
        stack += im
    return seen, ext
mods = sys.argv[2:]
cl = {}
for m in mods:
    s, e = closure(m)
    tc = sorted(x for x in s if x.startswith('TCSlib'))
    cl[m] = set(tc)
    print(f"== {m}: {len(tc)} TCSlib modules in closure (incl. itself); external roots: {sorted(set(x.split('.')[0] for x in e))}")
    for x in tc: print('   ', x)
if len(mods) >= 2:
    a, b = mods[0], mods[1]
    print(f"\n{b} in closure({a})? {b in cl[a]}")
    print(f"{a} in closure({b})? {a in cl[b]}  (a cycle iff True when {a} imports {b})")
    print(f"added to closure({a}) by importing {b}: {sorted(cl[b] - cl[a])}")
