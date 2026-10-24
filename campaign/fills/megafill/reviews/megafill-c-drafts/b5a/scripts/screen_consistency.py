import re, sys
lines = open(sys.argv[1], encoding='utf-8').read().splitlines()
hdr = re.match(r"declarations screened: (\d+); copy pairs .*: (\d+); reproduced text: ([\d,]+) chars", lines[0])
nd, npairs, chars = int(hdr.group(1)), int(hdr.group(2)), int(hdr.group(3).replace(',', ''))
pat = re.compile(r"^   (\S+)::(\S+)  reproduces  (\S+)::(\S+): (\d+)/(\d+) = (\d+)%$")
rows = []
for l in lines[1:]:
    m = pat.match(l); assert m, l
    rows.append(m.groups())
tot = sum(int(r[4]) for r in rows)
print('header decls', nd, 'pairs', npairs, 'chars', chars)
print('rows', len(rows), 'sum numerators', tot, 'consistent:', len(rows) == npairs and tot == chars)
bad = [r for r in rows if not (int(r[4]) >= 60 and 2 * int(r[4]) >= int(r[5]))]
print('rows violating the >=60 and >=half rule:', len(bad))
pct = [r for r in rows if round(100 * int(r[4]) / int(r[5])) != int(r[6])]
print('rows whose percent does not match:', len(pct))
order_ok = all((int(a[4]) / int(a[5]), int(a[4])) >= (int(b[4]) / int(b[5]), int(b[4])) for a, b in zip(rows, rows[1:]))
print('sorted descending:', order_ok)
own = sys.argv[2]
mine = [r for r in rows if r[0] == own or r[2] == own]
within = [r for r in mine if r[0] == own and r[2] == own]
across = [r for r in mine if not (r[0] == own and r[2] == own)]
print(f'{own}: {len(mine)} pairs, within {len(within)} (>=90%: {sum(1 for r in within if int(r[6]) >= 90)}), across {len(across)} (>=90%: {sum(1 for r in across if int(r[6]) >= 90)}), max across {max(int(r[6]) for r in across) if across else None}')
for r in within:
    if int(r[6]) >= 90: print('  in>=90', r)
for r in across:
    if int(r[6]) >= 87: print('  across>=87', r)
files = sorted(set([r[0] for r in rows] + [r[2] for r in rows]))
print('files appearing in pairs:', len(files))
