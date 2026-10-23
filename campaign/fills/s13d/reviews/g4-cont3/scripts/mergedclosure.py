# usage: mergedclosure.py <graph.json> <changed-files-list>
# Prints the union of each changed module and its downstream closure, in dependency order,
# without the root TCSlib (replay rule).
import json, sys
g = json.load(open(sys.argv[1]))
cm = [l.strip()[:-5].replace('/', '.') for l in open(sys.argv[2]) if l.strip().endswith('.lean')]
rev = {}
for m, ds in g.items():
    for d in ds: rev.setdefault(d, []).append(m)
nodes = set()
for c in cm:
    st = [c]; nodes.add(c)
    while st:
        m = st.pop()
        for d in rev.get(m, []):
            if d not in nodes: nodes.add(d); st.append(d)
nodes.discard('TCSlib')
order, seen = [], set()
def visit(m):
    if m in seen: return
    seen.add(m)
    for d in sorted(g.get(m, [])):
        if d in nodes: visit(d)
    order.append(m)
for m in sorted(nodes): visit(m)
print(f'# {len(order)} modules (changed: {len(cm)}), dependency order, root TCSlib excluded')
for m in order: print(m.replace('.', '/'))
