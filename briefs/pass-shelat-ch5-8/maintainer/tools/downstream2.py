"""downstream2.py <root> <module>...: modules downstream of the targets (facades excluded, i.e. files
whose code is only imports), then the upstream closure of that set, in topological order:
'<path> DOWN|UP'."""
import sys, os, re
root = sys.argv[1]; targets = set(sys.argv[2:])
mods, facade = {}, set()
for dp, _, fs in os.walk(os.path.join(root, 'TCSlib')):
    for f in fs:
        if f.endswith('.lean'):
            p = os.path.join(dp, f); m = os.path.relpath(p, root)[:-5].replace('/', '.')
            src = open(p, encoding='utf-8').read()
            mods[m] = [x for x in re.findall(r'^import\s+(\S+)', src, re.M) if x.startswith('TCSlib')]
            code = re.sub(r'/-.*?-/', '', src, flags=re.S); code = re.sub(r'--[^\n]*', '', code)
            if all(l.startswith('import ') or not l.strip() for l in code.splitlines()): facade.add(m)
down = set(targets); changed = True
while changed:
    changed = False
    for m, imps in mods.items():
        if m not in down and m not in facade and any(i in down for i in imps): down.add(m); changed = True
need, st = set(), list(down)
while st:
    x = st.pop()
    if x in need: continue
    need.add(x); st.extend(mods.get(x, []))
order, seen = [], set()
def visit(x):
    if x in seen: return
    seen.add(x)
    for i in mods.get(x, []): visit(i)
    order.append(x)
for x in sorted(need): visit(x)
for x in order: print(x.replace('.', '/'), 'DOWN' if x in down else 'UP')
