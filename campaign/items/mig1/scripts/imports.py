import re, sys, glob, os, json
root = sys.argv[1]
G = {}
for f in glob.glob(root + '/TCSlib/**/*.lean', recursive=True):
    m = f[len(root) + 1:-5].replace('/', '.')
    G[m] = [l.split()[1] for l in open(f, encoding='utf-8') if l.startswith('import ')]
def clos(m):
    seen = set(); st = [m]
    while st:
        x = st.pop()
        for y in G.get(x, []):
            if y.startswith('TCSlib') and y not in seen: seen.add(y); st.append(y)
    return seen
json.dump({m: sorted(clos(m)) for m in G}, open('closure.json', 'w'))
B = 'TCSlib.Complexity.TuringMachine.'
for a in sys.argv[2:]:
    print(a, '->', [x.replace(B, '') for x in sorted(clos(B + a)) if x.startswith(B)])
rev = {}
for m in G:
    for y in clos(m): rev.setdefault(y, set()).add(m)
for t in ['Build.Catalog', 'Build.Primitives', 'Build.Loop', 'Composition', 'Build.Wrappers']:
    print('importers of', t, len(rev.get(B + t, ())))
