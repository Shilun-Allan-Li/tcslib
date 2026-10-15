import json, sys
g = json.load(open(sys.argv[1]))
mode = sys.argv[2]   # up | down
targets = sys.argv[3:]
for t in targets:
    assert t in g, t
order = []
seen = set()
def visit(m):
    if m in seen: return
    seen.add(m)
    for d in g.get(m, []):
        if d in g: visit(d)
    order.append(m)
for m in sorted(g): visit(m)   # global topo order
if mode == 'up':
    need = set()
    def up(m):
        if m in need: return
        need.add(m)
        for d in g[m]:
            if d in g: up(d)
    for t in targets: up(t)
    res = [m for m in order if m in need]
else:
    rev = {m: [] for m in g}
    for m, ds in g.items():
        for d in ds:
            if d in rev: rev[d].append(m)
    need = set()
    def down(m):
        if m in need: return
        need.add(m)
        for u in rev[m]: down(u)
    for t in targets: down(t)
    res = [m for m in order if m in need]
for m in res: print(m)
