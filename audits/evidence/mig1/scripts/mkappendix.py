import json, collections
g = json.load(open('groups.json')); dep = json.load(open('deps.json')); ub = dep['usedby']
ident = set()
# recompute code-identical set (from verbatim3 logic)
exec(open('verbatim.py').read().split("idx = {}")[0].replace("C = sys.argv[1]", "C = '/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad/wt-mig1/TCSlib/Complexity'"))
idx = {}
for k in files:
    if k == 'Catalog': continue
    for d in decl[k]: idx.setdefault(d['name'], []).append((k, d))
def norm(l): return l.replace('f2_', '').rstrip()
for d in decl['Catalog']:
    if not d['name'].startswith('f2_'): continue
    b = d['name'][3:]
    if b not in idx: continue
    k, sd = idx[b][0]
    a0 = [norm(x) for x in src['Catalog'][d['line']-1:d['end']] if x.strip()]
    b0 = [x.rstrip() for x in src[k][sd['line']-1:sd['end']] if x.strip()]
    if a0 == b0: ident.add(d['name'])
home = {
 'computesFunInTime_id_spaceUsed': 'computesFunInTime_id', 'computesFunInTime_const_spaceUsed': 'computesFunInTime_const',
 'computesFunInTime_prepend_spaceUsed': 'computesFunInTime_prepend (and pairEncodeFixed)', 'computesFunInTime_incFixed_spaceUsed': 'computesFunInTime_incFixed',
 'computesFunInTime_pairDup_spaceUsed': 'computesFunInTime_pairDup', 'computesFunInTime_pairValid_spaceUsed': 'computesFunInTime_pairValid',
 'computesFunInTime_pairConcat_spaceUsed': 'computesFunInTime_pairFst, pairSnd, pairConcat', 'computesFunInTime_polyUnary_spaceUsed': 'computesFunInTime_polyUnary (and polyBits)',
 'computesFunInTime_lengthBits_spaceUsed': 'computesFunInTime_lengthBits / Complexity.timeConstructible_id', 'computesFunInTime_pairLenCheck_spaceUsed': 'computesFunInTime_pairLenCheck',
 'computesFunInTime_stripLast_spaceUsed': 'computesFunInTime_stripLast', 'exists_loopTM_spaceUsed': 'exists_loopTM / exists_loopCfgTM / exists_loopFindTM (the loop host)',
 'computesFunInTime_splitSolve_spaceUsed': 'computesFunInTime_splitSolve', 'computesFunInTime_cond_spaceUsed': 'computesFunInTime_cond',
 '(no public row uses it)': '—',
}
out = []
tot = 0
for grp, items in g.items():
    others = collections.Counter()
    for it in items:
        for r in ub.get(it[1], []):
            if r != grp: others[r] += 1
    lines = sum(x[3] for x in items)
    tot += len(items)
    cnt = collections.Counter('=' if x[1] in ident else ('≈' if x[2] else 'new') for x in items)
    out.append(f"#### {grp}: {len(items)} declarations, {lines} lines (code only)\n")
    out.append(f"Re-derives the witness of `{home[grp]}`. Copies: {cnt['=']} identical, {cnt['≈']} modified, {cnt['new']} with no same-named source." + (f" Also used by: " + ', '.join(f'`{r}` ({n})' for r, n in sorted(others.items())) + '.' if others else '') + "\n")
    cells = []
    for (line, name, src_, n, nrows) in items:
        tag = '=' if name in ident else ('≈' if src_ else 'new')
        s = f"`{name}` {line}"
        if tag != '=': s += f" ({tag})"
        cells.append(s)
    out.append(', '.join(cells) + '\n')
open('appendix.md', 'w').write('\n'.join(out))
print(tot, len(ident))
