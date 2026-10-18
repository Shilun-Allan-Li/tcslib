import json, sys
g = json.load(open(sys.argv[1])); root = sys.argv[2]
up, st = set(), [root]
while st:
    m = st.pop()
    for d in g.get(m, []):
        if d not in up: up.add(d); st.append(d)
rev = {}
for m, ds in g.items():
    for d in ds: rev.setdefault(d, []).append(m)
down, st = set(), [root]
while st:
    m = st.pop()
    for d in rev.get(m, []):
        if d not in down: down.add(d); st.append(d)
# topological order of downstream (including root)
nodes = down | {root}
order, seen = [], set()
def visit(m):
    if m in seen: return
    seen.add(m)
    for d in g.get(m, []):
        if d in nodes: visit(d)
    order.append(m)
for m in sorted(nodes): visit(m)
print('upstream', len(up)); print('\n'.join('  U ' + m for m in sorted(up)))
print('downstream closure (incl. root, dependency order):', len(order)); print('\n'.join('  D ' + m for m in order))
