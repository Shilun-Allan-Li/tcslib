"""Base -> landed transitions of every pair, and the disposition of every payback ledger row.

For each pair id in the base or the landed screen: its class and group at each tree, and its
status: present at both (with the max shared characters at each), removed (base only), or new at
the landed tree. Then, for each row of the payback's ledger map (34 P1/P1+ pair rows, L049, the 4
manual rows), the map's copy-side action and the screens' verdict on the pair.
usage: python3 -I transitions.py <pairs3-base.tsv> <classify3-base.tsv> <pairs3-landed.tsv>
       <classify3-landed.tsv> <ledger-map.md> <out-transitions.tsv> <out-dispositions.tsv>"""
import re, sys
pb, cb, pl, cl, lmap, otr, odi = sys.argv[1:8]
rd = lambda f: {c[0]: c for c in (l.rstrip('\n').split('\t') for l in open(f, encoding='utf-8')) if c[0] != 'pid'}
PB, CB, PL, CL = rd(pb), rd(cb), rd(pl), rd(cl)
ids = sorted(set(PB) | set(PL))
cnt = {}
with open(otr, 'w', encoding='utf-8') as f:
    f.write('pid\tcat\tA\tB\tstatus\tbase_class\tbase_group\tbase_shared\tlanded_class\tlanded_group\tlanded_shared\n')
    for i in ids:
        b, l = PB.get(i), PL.get(i); r = b or l
        st = 'present' if b and l else ('removed' if b else 'new-at-landed')
        bc = CB[i] if b else None; lc = CL[i] if l else None
        k = (r[1], st, (bc or lc)[2]); cnt[k] = cnt.get(k, 0) + 1
        f.write(f"{i}\t{r[1]}\t{r[2]}::{r[3]}\t{r[7]}::{r[8]}\t{st}\t{bc[2] if bc else '-'}\t{bc[4] if bc else '-'}\t{b[13] if b else '-'}\t"
                f"{lc[2] if lc else '-'}\t{lc[4] if lc else '-'}\t{l[13] if l else '-'}\n")
for k in sorted(cnt): print('transition', k, cnt[k])
rows = []
for line in open(lmap, encoding='utf-8'):
    if not line.startswith('| ') or line.startswith('| Row') or line.startswith('|---'): continue
    c = [x.strip() for x in line.strip().strip('|').split('|')]
    rows.append(c)
with open(odi, 'w', encoding='utf-8') as f:
    f.write('row\tgroup_family\tcopy\tcopy_action\toriginal\toriginal_action\tshared_after\tbase_screen\tlanded_screen\n')
    for c in rows:
        rid = c[0]; bs = 'pair present' if rid in PB else ('-' if not re.match(r'^[SIL]\d{3}$', rid) else 'pair absent')
        ls = 'pair present' if rid in PL else ('-' if not re.match(r'^[SIL]\d{3}$', rid) else 'pair absent')
        f.write('\t'.join([rid, c[1], c[2], c[3], c[6], c[7], c[10], bs, ls]) + '\n')
print('ledger-map rows', len(rows))
