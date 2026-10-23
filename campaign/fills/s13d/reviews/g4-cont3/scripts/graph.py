# usage: graph.py <worktree> <module> [changed-files-list]
# Builds the TCSlib import graph of <worktree>, prints the upstream closure of <module>, the
# modules downstream of it (dependency order), and which of the listed changed files fall in each.
import os, re, sys, json
wt, root = sys.argv[1], sys.argv[2]
changed = [l.strip() for l in open(sys.argv[3])] if len(sys.argv) > 3 else []
IMP = re.compile(r'^\s*import\s+(.+)$')
g = {}
for dp, dn, fn in os.walk(os.path.join(wt, 'TCSlib')):
    for f in fn:
        if f.endswith('.lean'):
            p = os.path.join(dp, f); m = os.path.relpath(p, wt)[:-5].replace(os.sep, '.')
            deps = []
            for l in open(p, encoding='utf-8'):
                mm = IMP.match(l)
                if mm: deps += [x for x in mm.group(1).split() if x.startswith('TCSlib')]
                elif l.strip() and not l.startswith('--') and not l.startswith('/-') and deps: pass
            g[m] = deps
top = os.path.join(wt, 'TCSlib.lean')
if os.path.isfile(top):
    g['TCSlib'] = [x for l in open(top) for x in (IMP.match(l).group(1).split() if IMP.match(l) else []) if x.startswith('TCSlib')]
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
print('modules in graph:', len(g))
print('upstream of', root, ':', len(up))
for m in sorted(up): print('  U', m)
print('downstream of', root, '(excluding root):', len(down))
for m in sorted(down): print('  D', m)
if changed:
    cm = [c[:-5].replace('/', '.') for c in changed if c.endswith('.lean')]
    print('changed .lean modules:', len(cm))
    for c in cm: print('  C', c, '| upstream' if c in up else '', '| downstream' if c in down else '', '| root' if c == root else '')
json.dump(g, open(os.path.join(os.path.dirname(os.path.abspath(sys.argv[0])), '..', 'out', 'graph-' + os.path.basename(wt.rstrip('/')) + '.json'), 'w'), indent=0, sort_keys=True)
