import sys, os, re
root = sys.argv[1]; targets = set(sys.argv[2:])
mods = {}
for dp, _, fs in os.walk(os.path.join(root, 'TCSlib')):
    for f in fs:
        if f.endswith('.lean'):
            p = os.path.join(dp, f); m = os.path.relpath(p, root)[:-5].replace('/', '.')
            mods[m] = [x for x in re.findall(r'^import\s+(\S+)', open(p, encoding='utf-8').read(), re.M) if x.startswith('TCSlib')]
for top in ['TCSlib.lean']:
    mods['TCSlib'] = [x for x in re.findall(r'^import\s+(\S+)', open(os.path.join(root, top), encoding='utf-8').read(), re.M)]
down = set(targets); changed = True
while changed:
    changed = False
    for m, imps in mods.items():
        if m not in down and any(i in down for i in imps): down.add(m); changed = True
# upstream closure of down, topological order
need = set(); st = list(down)
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
for x in order:
    if x != 'TCSlib': print(x.replace('.', '/'), 'DOWN' if x in down else 'UP')
