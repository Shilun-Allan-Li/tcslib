import json, re, sys, collections
C = sys.argv[1]
L = open(C + '/TuringMachine/Build/Catalog.lean', encoding='utf-8').read().split('\n')
D = json.load(open('d_Catalog.json'))
names = {d['name'] for d in D}
def strip(s):
    s = re.sub(r'/-.*?-/', ' ', s, flags=re.S); return re.sub(r'--[^\n]*', ' ', s)
uses = {}
for d in D:
    body = strip('\n'.join(L[d['line'] - 1:d['end']]))
    toks = set(re.findall(r"[A-Za-z_][\w'.]*", body))
    u = set()
    for t in toks:
        for part in [t, t.split('.')[-1]]:
            if part in names and part != d['name']: u.add(part)
    uses[d['name']] = u
priv = {d['name'] for d in D if d['private']}
region = [d for d in D if 1779 <= d['line'] <= 11361]
pubr = [d['name'] for d in region if not d['private']]
def closure(n):
    seen = set(); st = [n]
    while st:
        x = st.pop()
        for y in uses.get(x, ()):
            if y in priv and y not in seen: seen.add(y); st.append(y)
    return seen
cl = {p: closure(p) for p in pubr}
# also closure of public rows outside region (R3 rows and Part 3) to see whether they use f2_
outside = [d['name'] for d in D if not d['private'] and not (1779 <= d['line'] <= 11361)]
for p in outside:
    c = closure(p)
    f2 = [x for x in c if x.startswith('f2_') or x.startswith('a2_')]
    if f2: print('OUTSIDE', p, 'uses', len(f2), sorted(f2)[:5])
usedby = collections.defaultdict(list)
for p in pubr:
    for x in cl[p]: usedby[x].append(p)
regpriv = [d for d in region if d['private']]
unused = [d['name'] for d in regpriv if not usedby[d['name']]]
print('region private decls', len(regpriv), 'unused by any public row in region', len(unused), unused[:20])
# also check whether public rows outside the region use region privates
json.dump({'closure': {p: sorted(cl[p]) for p in pubr}, 'usedby': {k: v for k, v in usedby.items()}}, open('deps.json', 'w'), indent=0)
for p in pubr:
    c = cl[p]
    print(p, 'closure', len(c), 'f2', sum(1 for x in c if x.startswith('f2_')), 'a2', sum(1 for x in c if x.startswith('a2_')), 'other', sorted(x for x in c if not x.startswith(('f2_', 'a2_'))))
