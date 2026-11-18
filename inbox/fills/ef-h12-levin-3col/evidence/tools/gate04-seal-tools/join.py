"""join.py <declchanges.tsv> <attrib.tsv>...: per failing declaration, the candidates whose single
seal fails it, and the declaration's change status against the merge base (NEW/CHANGED/SAME)."""
import sys, re
chg = {}
for l in open(sys.argv[1], encoding='utf-8'):
    p = l.rstrip('\n').split('\t')
    if len(p) == 5:
        a, b, c = p[3].split('-')
        chg[(p[0], int(b))] = (p[1], p[4])
fails = {}
for fn in sys.argv[2:]:
    for l in open(fn, encoding='utf-8'):
        p = l.rstrip('\n').split('\t')
        if len(p) < 4 or p[2] == 'PASS':
            continue
        if p[2] == 'TIMEOUT':
            fails.setdefault((p[0], 'TIMEOUT'), set()).add(p[1]); continue
        for d in p[3].split():
            nm, ln = d.rsplit('@', 1)
            fails.setdefault((p[0], int(ln)), set()).add(p[1])
for (path, ln) in sorted(fails, key=lambda k: (k[0], 10**9 if k[1] == 'TIMEOUT' else k[1])):
    if ln == 'TIMEOUT':
        print(f"{path}\tTIMEOUT\t-\t{' '.join(sorted(fails[(path, ln)]))}"); continue
    name, st = chg.get((path, ln), ('?', '?'))
    print(f"{path}\t{name}@{ln}\t{st}\t{' '.join(sorted(fails[(path, ln)]))}")
