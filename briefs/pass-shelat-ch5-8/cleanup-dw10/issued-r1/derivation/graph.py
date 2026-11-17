"""graph.py <repo> <rev> <outdir>: import graph, depth-first post-order from TCSlib.lean
(imports in file order), declaration index and syntactic admissions at <rev>, from git objects.
Writes full-order.txt, decls.tsv, sorries.tsv, imports.tsv."""
import sys, os, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import leanindex as L

repo, rev, outdir = sys.argv[1:4]
os.makedirs(outdir, exist_ok=True)
paths = [p for p in L.git(repo, 'ls-tree', '-r', '--name-only', rev, '--', 'TCSlib', 'TCSlib.lean').split('\n')
         if p.endswith('.lean')]
src = L.blobs(repo, rev, paths)
mod = lambda p: p[:-5].replace('/', '.')
byname = {mod(p): p for p in paths}
imps = {m: L.imports(src[p]) for m, p in byname.items()}
order, seen = [], set()


def visit(m):
    stack = [(m, iter(imps.get(m, [])))]
    seen.add(m)
    while stack:
        cur, it = stack[-1]
        nxt = next((x for x in it if x in byname and x not in seen), None)
        if nxt is None:
            stack.pop(); order.append(cur)
        else:
            seen.add(nxt); stack.append((nxt, iter(imps.get(nxt, []))))


visit('TCSlib')
with open(f'{outdir}/full-order.txt', 'w') as f:
    f.write('\n'.join(m.replace('.', '/') for m in order) + '\n')
with open(f'{outdir}/imports.tsv', 'w') as f:
    for m in sorted(imps):
        f.write(m + '\t' + ' '.join(imps[m]) + '\n')
with open(f'{outdir}/decls.tsv', 'w') as f:
    for m in sorted(byname):
        for full, kind, priv, line in L.decls(src[byname[m]]):
            f.write(f'{byname[m]}\t{line}\t{kind}\t{int(priv)}\t{full}\n')
with open(f'{outdir}/sorries.tsv', 'w') as f:
    for m in sorted(byname):
        for name, n in sorted(L.sorries(src[byname[m]]).items()):
            f.write(f'{m.replace(".", "/")}\t{name}\t{n}\n')
unreached = sorted(set(byname) - seen)
json.dump({'rev': rev, 'files': len(paths), 'reachable_from_TCSlib': len(order),
           'unreached': unreached}, open(f'{outdir}/graph-summary.json', 'w'), indent=1)
print(len(paths), 'files;', len(order), 'reachable;', len(unreached), 'unreached')
