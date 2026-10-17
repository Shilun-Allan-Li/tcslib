"""Consumer totals per row, and the difference from a previous measurement. Read-only.

Usage: python3 -I rowtotals.py <consumer-names.json> <consumers.json> <previous consumers.json>

The 53 public machine-existential rows are the consumer names minus the six R3 rows, the two
rewind head lemmas, `redirectTM_spaceUsedByTape` and `timeConstructible_id`; the 34 home rows are
those of them homed outside Catalog. For each row: external code citations (count and files)
now and before, every citation site that is new or gone, and every docstring or comment mention
that is new or gone (consumers.py's `doc`). Prints the aggregate lines `rows53: <citations> in
<files> files`, `rows34: ...` and `doc mentions: ...` last.
"""
import json
import sys

names = json.load(open(sys.argv[1], encoding='utf-8'))
now = json.load(open(sys.argv[2], encoding='utf-8'))
old = json.load(open(sys.argv[3], encoding='utf-8'))
NOT_ROWS = {'transferTM_run', 'copyTM_run', 'clearTM_run', 'compareTM_run', 'incrementTM_run_succ',
            'incrementTM_run_overflow', 'rewind_scan_heads', 'rewind_heads',
            'redirectTM_spaceUsedByTape', 'timeConstructible_id'}
CAT = 'TCSlib.Complexity.TuringMachine.Build.Catalog'
rows = [(h, n) for h, n in names if n not in NOT_ROWS]
home = [(h, n) for h, n in rows if h != CAT]
assert len(rows) == 53 and len(home) == 34, (len(rows), len(home))


def tot(db, sel):
    c = sum(n for _, s in sel for _, _, n in db[s]['external'])
    f = {m for _, s in sel for m, _, _ in db[s]['external']}
    return c, f


for h, n in names:
    a = {(m, l) for m, l, _ in now[n]['external']}
    b = {(m, l) for m, l, _ in old[n]['external']}
    ca = sum(k for _, _, k in now[n]['external'])
    cb = sum(k for _, _, k in old[n]['external'])
    mark = '' if (ca, len({m for m, _ in a})) == (cb, len({m for m, _ in b})) else '  CHANGED'
    print(f"{n}: declared {len(now[n]['declared'])}; external {ca} in {len({m for m, _ in a})} files"
          f" (before {cb} in {len({m for m, _ in b})}){mark}")
    for m, l in sorted(a - b):
        print(f'    new citation site: {m}:{l}')
    for m, l in sorted(b - a):
        print(f'    gone citation site: {m}:{l}')
    da = {(m, l) for m, l, _ in now[n]['doc']}
    db = {(m, l) for m, l, _ in old[n]['doc']}
    for m, l in sorted(da - db):
        print(f'    new docstring/comment mention: {m}:{l}')
    for m, l in sorted(db - da):
        print(f'    gone docstring/comment mention: {m}:{l}')
dn = sum(k for _, s in names for _, _, k in now[s]['doc'])
do = sum(k for _, s in names for _, _, k in old[s]['doc'])
for label, sel in [('rows53', rows), ('rows34', home)]:
    c, f = tot(now, sel)
    c0, f0 = tot(old, sel)
    print(f'{label}: {c} in {len(f)} files (before {c0} in {len(f0)}; new files: '
          f'{sorted(x.split(".", 2)[2] for x in f - f0)})')
print(f'doc mentions of the {len(names)} names: {dn} (before {do})')
