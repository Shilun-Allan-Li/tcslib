"""Family tables: (1) round 1's 45 internal components (connected components of all cross-file
new/new pairs), each with its pairs' classes, family class (S if any S pair, else G if any G,
else N), representative pair and logical family; (2) same-file components per file; (3) the
logical K-families with their pair counts.
usage: python3 -I families.py <pairs.tsv> <classify.tsv> <kfam.tsv> <out>"""
import sys
ptsv, ctsv, kf, dst = sys.argv[1:5]
rows = [l.rstrip('\n').split('\t') for l in open(ptsv, encoding='utf-8')][1:]
cls = {c[0]: c for c in (l.rstrip('\n').split('\t') for l in open(ctsv, encoding='utf-8')) if c[0] != 'pid'}
kmap = {}
for l in open(kf, encoding='utf-8'):
    if l.startswith('#') or not l.strip(): continue
    ids, k = l.rstrip('\n').split('\t')
    for i in ids.split(): kmap[i] = k
short = lambda p, n: p.replace('TCSlib/Complexity/', '').replace('SpaceComplexity/', '').replace('ClassPSPACE/', '').replace('.lean', '') + '::' + n
o = open(dst, 'w', encoding='utf-8')
def comps(cat, keyf):
    adj = {}; edges = {}
    for c in rows:
        if c[1] != cat: continue
        A, B = (c[2], c[3]), (c[7], c[8])
        adj.setdefault(A, set()).add(B); adj.setdefault(B, set()).add(A)
        edges.setdefault(A, []).append(c); edges.setdefault(B, []).append(c)
    seen = set(); out = []
    for v in sorted(adj):
        if v in seen: continue
        st = [v]; comp = []; seen.add(v)
        while st:
            u = st.pop(); comp.append(u)
            for x in adj[u]:
                if x not in seen: seen.add(x); st.append(x)
        ps = {c[0]: c for u in comp for c in edges[u]}
        out.append((sorted(comp), [ps[k] for k in sorted(ps)]))
    return out
for cat, title, pre in (('internal', 'Internal components (cross-file pairs among the 73 added files)', 'IC'),
                        ('same', 'Same-file components (pairs inside one added file)', 'SC')):
    cs = comps(cat, None)
    cs.sort(key=lambda x: (-len(x[0]), x[0][0]))
    o.write(f'## {title}: {len(cs)} components, {sum(len(p) for _, p in cs)} pairs\n')
    o.write('id | members | pairs (S/G/N) | family class | representative pair (max shared) | logical families\n')
    for i, (comp, ps) in enumerate(cs, 1):
        cnt = {k: sum(1 for c in ps if cls[c[0]][2] == k) for k in 'SGN'}
        fc = 'substantive' if cnt['S'] else ('small genuine' if cnt['G'] else 'incidental')
        rep = max(ps, key=lambda c: int(c[13]))
        ks = sorted({kmap[c[0]] for c in ps if c[0] in kmap})
        o.write(f'{pre}{i:02d} | {", ".join(short(*m) for m in comp)} | {len(ps)} ({cnt["S"]}/{cnt["G"]}/{cnt["N"]}) | {fc} | {rep[0]} {short(rep[2], rep[3])} ~ {short(rep[7], rep[8])}, {rep[13]} shared | {", ".join(ks) or "-"}\n')
    o.write('\n')
o.write('## Logical families (K): pairs by category and class\n')
for k in sorted(set(kmap.values()), key=lambda s: int(s[1:])):
    ps = [p for p, kk in kmap.items() if kk == k]
    by = {}
    for p in ps:
        c = cls[p]; by[(c[1], c[2])] = by.get((c[1], c[2]), 0) + 1
    o.write(f'{k}: {len(ps)} pairs; ' + ', '.join(f'{a} {b} {n}' for (a, b), n in sorted(by.items())) + '\n')
# sanity: every S/G internal or same-file pair has a K family
miss = [c[0] for c in rows if c[1] != 'lib' and cls[c[0]][2] in 'SG' and c[0] not in kmap]
o.write(f'\nS/G internal or same-file pairs without a logical family: {miss or "none"}\n')
bad = [p for p in kmap if cls[p][2] == 'N']
o.write(f'pairs mapped to a family but classified N: {bad or "none"}\n')
print('ok', len(miss), len(bad))
