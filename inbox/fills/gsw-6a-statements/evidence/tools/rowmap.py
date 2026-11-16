"""rowmap.py <file>...: maps r3 target rows to declarations. A declaration's docstring that names a row
(`C12`, `F7`, `N3`, ... as `**C12.**`, `C12.` or `(C12)` at its start) is assigned to that row; for
every declaration also prints whether its body is `sorry` (target) or proved."""
import sys, re
rows = {}
for p in sys.argv[1:]:
    s = open(p, encoding='utf8').read()
    for m in re.finditer(r'/--(.*?)-/\s*\n((?:@\[[^\]]*\]\s*)?(?:private\s+|noncomputable\s+)*(theorem|def|structure|instance|abbrev)\s+(\S+))', s, re.S):
        doc, kind, name = m.group(1), m.group(3), m.group(4)
        rest = s[m.end():]
        nxt = re.search(r'\n(?:/--|theorem |def |end |section |namespace |instance |structure |private |noncomputable |@\[|/-!)', rest)
        body = rest[:nxt.start()] if nxt else rest
        status = 'sorry' if re.search(r'\bsorry\b', body) else 'proved'
        mm = re.match(r'\s*\**\s*\(?([CFN])(\d+)[.,)]', doc)
        row = f'{mm.group(1)}{mm.group(2)}' if mm else None
        if row: rows.setdefault(row, []).append((name, kind, status, p.split('/')[-1]))
        print(f'{row or "-"}\t{name}\t{kind}\t{status}\t{p}')
print('== row map')
for r in sorted(rows, key=lambda r: (r[0], int(r[1:]))):
    print(r + '\t' + '; '.join(f'{n} ({s})' for n, k, s, f in rows[r]))
