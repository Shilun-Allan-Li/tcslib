import sys, re
# usage: axsum.py <axiom out>...: per declaration, its axiom set (normalized), for each file side by side
res = []
for p in sys.argv[1:]:
    t = open(p, encoding='utf-8').read()
    d = {}
    for m in re.finditer(r"'([^']+)' (depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", t):
        n = re.sub(r'^_private\.[^.]+(\.[^.]+)*?\.0\.', '', m.group(1))
        ax = sorted(a.strip() for a in (m.group(3) or '').replace('\n', ' ').split(',') if a.strip())
        d.setdefault(n, ax)
    res.append(d)
names = list(res[0])
std = {'propext', 'Classical.choice', 'Quot.sound'}
print('declaration | ' + ' | '.join(p.split('/')[-1] for p in sys.argv[1:]))
for n in names:
    cells = []
    for d in res:
        a = d.get(n)
        cells.append('-' if a is None else ('[' + ', '.join(a) + ']') + ('' if set(a) <= std else '  <-- NON-STANDARD'))
    print(n, '|', ' | '.join(cells))
