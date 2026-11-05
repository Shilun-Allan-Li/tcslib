import os, re, sys
root, target = sys.argv[1], sys.argv[2]
mods = {}
for dp, dn, fn in os.walk(os.path.join(root, 'TCSlib')):
    for f in fn:
        if f.endswith('.lean'):
            p = os.path.join(dp, f); m = os.path.relpath(p, root)[:-5]
            imps = []
            for line in open(p, encoding='utf-8'):
                mm = re.match(r'^import\s+(\S+)', line.strip())
                if mm and mm.group(1).startswith('TCSlib'):
                    imps.append(mm.group(1).replace('.', '/'))
            mods[m] = imps
for f in os.listdir(root):
    if f.endswith('.lean'):
        imps=[]
        for line in open(os.path.join(root,f), encoding='utf-8'):
            mm = re.match(r'^import\s+(\S+)', line.strip())
            if mm and mm.group(1).startswith('TCSlib'): imps.append(mm.group(1).replace('.', '/'))
        mods[f[:-5]] = imps
down = {target}; changed = True
while changed:
    changed = False
    for m, imps in mods.items():
        if m not in down and any(i in down for i in imps):
            down.add(m); changed = True
# topological order among down
order = []; seen = set()
def visit(m):
    if m in seen: return
    seen.add(m)
    for i in mods.get(m, []):
        if i in down: visit(i)
    order.append(m)
for m in sorted(down): visit(m)
print("modules:", len(mods))
print("downstream closure of", target, "(topological):")
for m in order: print(" ", m, "direct importers of target" if target in mods.get(m, []) else "")
# upstream closure size
up=set(); st=[target]
while st:
    m=st.pop()
    for i in mods.get(m,[]):
        if i not in up: up.add(i); st.append(i)
print("upstream closure size:", len(up))
