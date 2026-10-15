import json, re, sys, collections
C = sys.argv[1]; key = sys.argv[2]; path = sys.argv[3]
L = open(C + '/' + path, encoding='utf-8').read().split('\n')
D = json.load(open('d_' + key + '.json'))
names = {d['name'] for d in D}
def strip(s):
    s = re.sub(r'/-.*?-/', ' ', s, flags=re.S); return re.sub(r'--[^\n]*', ' ', s)
uses = {}
for d in D:
    body = strip('\n'.join(L[d['line'] - 1:d['end']]))
    toks = set(re.findall(r"[A-Za-z_][\w'.]*", body))
    uses[d['name']] = {p for t in toks for p in (t, t.split('.')[-1]) if p in names and p != d['name']}
priv = {d['name'] for d in D if d['private']}
pub = [d['name'] for d in D if not d['private']]
def closure(n):
    seen = set(); st = [n]
    while st:
        x = st.pop()
        for y in uses.get(x, ()):
            if y in priv and y not in seen: seen.add(y); st.append(y)
    return seen
cl = {p: closure(p) for p in pub}
ub = collections.defaultdict(set)
for p in pub:
    for x in cl[p]: ub[x].add(p)
span = {d['name']: d['end'] - d['line'] + 1 for d in D}
targets = sys.argv[4].split(',') if len(sys.argv) > 4 else []
for t in targets:
    excl = [x for x in cl[t] if ub[x] == {t}]
    print(f"{t}: closure {len(cl[t])} privates ({sum(span[x] for x in cl[t])} code lines); exclusively used by it: {len(excl)} ({sum(span[x] for x in excl)} code lines)")
unused = [d['name'] for d in D if d['private'] and not ub[d['name']] and d['kind'] not in ('instance',)]
print('privates used by no public decl (instances excluded):', len(unused), sum(span[x] for x in unused), unused[:40])
