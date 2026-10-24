import re, sys
src = open(sys.argv[1], encoding='utf-8').read()
probe = set(l.strip() for l in open(sys.argv[2]))
names = set()
for m in re.finditer(r'`([^`]+)`', src):
    tok = m.group(1)
    for w in re.findall(r"[A-Za-z_][A-Za-z0-9_'.₀-₉]*", tok):
        if '.' in w or w[0].islower():
            names.add(w)
# normalise: the probe names are fully qualified
short = {}
for p in probe:
    parts = p.split('.')
    for i in range(len(parts)):
        short.setdefault('.'.join(parts[i:]), set()).add(p)
out = []
for n in sorted(names):
    n2 = n.rstrip('.')
    if n2 in short: continue
    out.append(n2)
print('\n'.join(out))
