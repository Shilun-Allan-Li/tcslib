# scantab.py (dw10-seal-inventory, Claude lead, 2026-11-17): NEW. Flattens scan/<part>/explicit.json (the parts b1, b2a,
# b2b, b3, b4, b5; b2-attempt1 excluded) into the brief's evidence/scan.tsv: path, declaration, line, tactic, item, kind
# (scan2 classification and subkind), home, foreign (yes = a TCSlib definition of another file, not an abbreviation,
# reducible definition or projection; notation = such a definition that is an abbreviation/reducible/projection;
# no otherwise: own-file definitions OWNED_DEFINITION, local binders and unresolved names LOCAL_OR_UNRESOLVED,
# theorems, constructors, core/Mathlib definitions), tier, part.
# Usage: python3 -I scantab.py <evidence> <out.tsv>
import sys, os, json, glob
ev, outp = sys.argv[1:3]
tier = {l.split('\t')[2]: l.split('\t')[3] for l in open(os.path.join(ev, 'collect/batches.tsv')).read().split('\n')[1:] if l}
rows = []
for f in sorted(glob.glob(os.path.join(ev, 'scan/b*/explicit.json'))):
    part = f.split('/')[-2]
    if 'attempt' in part: continue
    for it in json.load(open(f))['items']:
        c = it['classification']; sk = it['subkind']
        fo = 'no'
        if c == 'FOREIGN_TCSLIB_DEFINITION': fo = 'notation' if sk in ('abbrev', 'reducible', 'projection') else 'yes'
        rows.append([it['file'], it['declaration'] or '-', str(it['line']), it['tactic'], it['item'], f'{c}/{sk}', it.get('resolved_home') or '-', fo, tier.get(it['file'], '-'), part])
with open(outp, 'w') as o:
    o.write('path\tdeclaration\tline\ttactic\titem\tkind\thome\tforeign\ttier\tpart\n')
    for r in rows: o.write('\t'.join(x.replace('\t', ' ').replace('\n', ' ') for x in r) + '\n')
import collections
print(len(rows), collections.Counter(r[7] for r in rows))
