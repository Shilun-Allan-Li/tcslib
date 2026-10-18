import json, sys
exec(open('verbatim.py').read().split("idx = {}")[0])
idx = {}
for k in files:
    if k == 'Catalog': continue
    for d in decl[k]: idx.setdefault(d['name'], []).append((k, d))
def norm(l): return l.replace('f2_', '').rstrip()
ident = identd = 0; nid = 0; nidd = 0; tot = 0; totd = 0; diffs = []
for d in decl['Catalog']:
    if not d['name'].startswith('f2_'): continue
    base = d['name'][3:]
    if base not in idx: continue
    k, sd = idx[base][0]
    s, e = with_doc(src['Catalog'], d); ss, se = with_doc(src[k], sd)
    a = [norm(x) for x in src['Catalog'][d['line']-1:e]]; b = [x.rstrip() for x in src[k][sd['line']-1:se]]
    ad = [norm(x) for x in src['Catalog'][s:e]]; bd = [x.rstrip() for x in src[k][ss:se]]
    # code identity ignoring a leading 'private ' difference
    a0 = [x for x in a if x.strip()]; b0 = [x for x in b if x.strip()]
    if a0 == b0: nid += 1; ident += len(ad)
    else: diffs.append((d['line'], d['name'], k, len(a0), len(b0)))
    if ad == bd: nidd += 1; identd += len(ad)
print('same-named pairs', sum(1 for d in decl['Catalog'] if d['name'].startswith('f2_') and d['name'][3:] in idx))
print('code-identical decls (after f2_ strip)', nid, 'their lines incl docstrings', ident)
print('fully identical incl docstrings', nidd, 'lines', identd)
print('differing', len(diffs))
for x in diffs[:80]: print(x)
