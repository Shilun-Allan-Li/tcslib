import json, sys, difflib, collections
exec(open('verbatim.py').read().split("idx = {}")[0])
# Variant A': best-matching source declaration for unmatched names (by matched-line count)
pool = []
for k in files:
    if k == 'Catalog': continue
    for d in decl[k]:
        ss, se = with_doc(src[k], d)
        pool.append((k, d['name'], [x.rstrip() for x in src[k][ss:se]], [x.rstrip() for x in src[k][d['line']-1:se]]))
def norm(l): return l.replace("f2_", "").rstrip()
per = json.load(open("verbatim.json"))
extra = 0; extra_d = 0; rows = []
for p in per:
    if p[2] is not None: continue
    d = next(x for x in decl['Catalog'] if x['line'] == p[0])
    s, e = with_doc(src['Catalog'], d)
    a = [norm(x) for x in src['Catalog'][s:e]]; ab = [norm(x) for x in src['Catalog'][d['line']-1:e]]
    best = (0, None)
    for (k, n, b, bb) in pool:
        if not (set(ab) & set(bb)): continue
        sm = difflib.SequenceMatcher(None, ab, bb, autojunk=False)
        m = sum(t.size for t in sm.get_matching_blocks())
        if m > best[0]: best = (m, (k, n, bb, b))
    m = best[0]
    md = 0
    if best[1]:
        sm = difflib.SequenceMatcher(None, a, best[1][3], autojunk=False); md = sum(t.size for t in sm.get_matching_blocks())
    rows.append((p[0], p[1], len(ab), m, best[1][0] + ':' + best[1][1] if best[1] else None))
    extra += m; extra_d += md
for r in rows: print(r)
print('extra code lines matched', extra, 'with docs', extra_d)
# Variant B: line-set membership against the union of source files (stripped, nonblank)
U = set()
for k in files:
    if k == 'Catalog': continue
    for x in src[k]: U.add(x.strip())
inb = inbd = tot = totd = 0
for d in decl['Catalog']:
    if not d['name'].startswith('f2_'): continue
    s, e = with_doc(src['Catalog'], d)
    for i in range(s, e):
        l = norm(src['Catalog'][i]).strip()
        code = i >= d['line'] - 1
        totd += 1; tot += code
        if l in U: inbd += 1; inb += code
print('membership: code', inb, '/', tot, '; with docs', inbd, '/', totd)
# region membership (lines 1779..11361)
reg = src['Catalog'][1778:11361]
print('region lines', len(reg), 'members', sum(1 for l in reg if norm(l).strip() in U), 'nonblank', sum(1 for l in reg if l.strip()))
