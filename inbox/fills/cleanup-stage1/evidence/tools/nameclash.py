"""nameclash.py <worktree> <touched.json> <outfile>: for every declaration of the unit (touched.json; private
included), list every declaration with the same last name component in any other TCSlib .lean file of the
worktree (keyword-line grep), with its namespace, and flag an EXACT full-name clash."""
import sys, os, re, json
wt, tj, out = sys.argv[1:4]
T = json.load(open(tj))['files']
own = set(T)
names = {}
for f, info in T.items():
    for d in info['declarations']:
        names[d['name']] = f
KW = re.compile(r'^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|nonrec|partial|unsafe)\s+)*(?:theorem|lemma|def|abbrev|structure|inductive|instance|class|opaque|axiom)\s+([^\s(:{\[]+)')
idx = {}
for r, ds, fs in os.walk(os.path.join(wt, 'TCSlib')):
    for fn in fs:
        if not fn.endswith('.lean'): continue
        p = os.path.relpath(os.path.join(r, fn), wt)
        if p in own: continue
        ns = []
        for i, l in enumerate(open(os.path.join(wt, p), encoding='utf-8')):
            m = re.match(r'^namespace\s+(\S+)', l)
            if m: ns.append(m.group(1)); continue
            m = re.match(r'^end\s+(\S+)\s*$', l)
            if m and ns and ns[-1] == m.group(1): ns.pop(); continue
            m = KW.match(l)
            if m:
                n = m.group(1); full = n[7:] if n.startswith('_root_.') else '.'.join(ns + [n])
                idx.setdefault(full.split('.')[-1], []).append((full, p, i + 1))
with open(out, 'w') as o:
    exact = 0
    for full, f in sorted(names.items()):
        short = full.split('.')[-1]
        hits = idx.get(short, [])
        ex = [h for h in hits if h[0] == full]
        exact += len(ex)
        auth = [h for h in hits if '.Authentication.' in h[0] + '.']
        o.write(f'{full}\t{f}\tsame-short-name {len(hits)}\tunder-Authentication {len(auth)}\tEXACT {len(ex)}\n')
        for h in auth: o.write(f'    {h[0]}\t{h[1]}:{h[2]}\n')
    o.write(f'RESULT exact full-name clashes: {exact}\n')
print(open(out).read().count('\n'), 'lines')
