import sys, os, re
root, mod = sys.argv[1], sys.argv[2]
changed = set(sys.argv[3:])
seen = set(); stack = [mod]
while stack:
    m = stack.pop()
    if m in seen: continue
    seen.add(m)
    p = os.path.join(root, m.replace('.', '/') + '.lean')
    if not os.path.exists(p): continue
    for l in open(p, encoding='utf-8'):
        mm = re.match(r'^import\s+(\S+)', l)
        if mm and mm.group(1).startswith('TCSlib'): stack.append(mm.group(1))
tc = sorted(s for s in seen if s.startswith('TCSlib'))
print('upstream closure of', mod, ':', len(tc), 'modules (itself included)')
ch = {c.replace('/', '.').removesuffix('.lean') for c in changed}
print('changed files in it:', sorted(ch & set(tc)))
