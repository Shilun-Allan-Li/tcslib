import json, collections
dep = json.load(open('deps.json')); D = json.load(open('d_Catalog.json'))
ver = {p[1]: p for p in json.load(open('verbatim.json'))}
cl = dep['closure']; ub = dep['usedby']
size = {p: len(v) for p, v in cl.items()}
groups = collections.defaultdict(list)
for d in D:
    n = d['name']
    if not n.startswith('f2_'): continue
    rows = ub.get(n, [])
    if not rows:
        g = '(no public row uses it)'
    else:
        g = min(rows, key=lambda r: (size[r], r))
    v = ver[n]
    groups[g].append((d['line'], n, v[2], v[5], len(rows)))
order = sorted(groups, key=lambda g: min(x[0] for x in groups[g]))
tot = 0
rowsout = []
for g in order:
    items = groups[g]
    lines = sum(x[3] for x in items)
    tot += len(items)
    srcs = collections.Counter(x[2] or 'new' for x in items)
    shared = sum(1 for x in items if x[4] > 1)
    rowsout.append((g, len(items), lines, dict(srcs), shared, items[0][0], items[-1][0]))
    print(f"{g}: {len(items)} decls, {lines} lines incl docstrings, sources {dict(srcs)}, used by >1 row: {shared}, lines {items[0][0]}-{items[-1][0]}")
print('total', tot)
json.dump({g: groups[g] for g in order}, open('groups.json', 'w'), indent=0)
