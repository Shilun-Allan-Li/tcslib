import os, re, sys
root, probe, pop = sys.argv[1], sys.argv[2], sys.argv[3]
names = re.findall(r'^#check @?(\S+)', open(probe, encoding='utf-8').read(), re.M)
tc = [n for n in names if n.startswith('Turing.') or n.startswith('Complexity.')]
files = {}
decl = {}
for dp, dn, fn in os.walk(os.path.join(root, 'TCSlib')):
    for f in fn:
        if not f.endswith('.lean'): continue
        p = os.path.join(dp, f); rel = os.path.relpath(p, root)
        for line in open(p, encoding='utf-8'):
            m = re.match(r'^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*(theorem|lemma|def|abbrev|structure|inductive|instance)\s+(\S+)', line)
            if m: decl.setdefault(m.group(2), set()).add(rel)
        # simps-generated
for n in tc:
    parts = n.split('.')
    hit = None
    for k in range(len(parts)):
        cand = '.'.join(parts[k:])
        if cand in decl: hit = decl[cand]; break
    if hit is None:
        # simps fields: strip last component
        base = '.'.join(parts[:-1]); 
        for k in range(len(parts)-1):
            cand = '.'.join(parts[k:-1])
            if cand in decl: hit = {f + ' (simps)' for f in decl[cand]}; break
    files[n] = sorted(hit) if hit else ['?']
popset = set(l.strip() for l in open(pop) if l.strip() and not l.startswith('#'))
used = {}
for n, fs in files.items():
    for f in fs:
        used.setdefault(f.replace(' (simps)', ''), []).append(n)
for f in sorted(used):
    mark = 'IN ' if f in popset else 'OUT'
    print(mark, f, len(used[f]), ' '.join(sorted(used[f])[:4]))
