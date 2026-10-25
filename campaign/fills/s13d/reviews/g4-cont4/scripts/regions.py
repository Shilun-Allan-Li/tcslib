import sys, difflib
a = open(sys.argv[1], encoding='utf-8').read().split('\n')
b = open(sys.argv[2], encoding='utf-8').read().split('\n')
# allowed base ranges (1-based, inclusive): (a) 127-1350, (b) 1391-1395 and 1408, (c) 1431-1438 and 1449
allowed = [(127, 1350, 'a'), (1391, 1395, 'b-status'), (1408, 1408, 'b-body'), (1431, 1438, 'c-status'), (1449, 1449, 'c-body')]
def region(i):  # i 1-based base line
    for lo, hi, n in allowed:
        if lo <= i <= hi: return n
    return None
sm = difflib.SequenceMatcher(a=a, b=b, autojunk=False)
bad = 0; hunks = 0
for tag, i1, i2, j1, j2 in sm.get_opcodes():
    if tag == 'equal': continue
    hunks += 1
    # base lines touched: i1+1..i2 (for replace/delete); for insert, insertion point between i1 and i1+1
    if i2 > i1:
        regs = {region(i) for i in range(i1 + 1, i2 + 1)}
    else:
        # insertion before base line i1+1: allowed if both neighbours (i1, i1+1) are in one allowed region,
        # or at a region boundary inside region (a) (insert after 1350 before 1351 counts as the home's end)
        regs = {region(i1) if i1 >= 1 else None, region(i1 + 1)}
        if region(i1) is not None: regs = {region(i1)}
        elif region(i1 + 1) is not None: regs = {region(i1 + 1)}
    ok = None not in regs
    if not ok: bad += 1
    print(f"{'OK ' if ok else 'OUT'} {tag:7} base {i1+1}-{i2} -> head {j1+1}-{j2} regions {sorted(r for r in regs if r) if ok else regs}")
print(f'hunks {hunks}; outside the owned regions: {bad}')
# key anchors in head
for k, l in enumerate(b, 1):
    if l.startswith('/-! ### The rows -/'): print('head: rows header at', k)
    if l.startswith('theorem exists_zone'): print('head:', l[:60], 'at', k)
for k, l in enumerate(a, 1):
    if l.startswith('/-! ### The rows -/'): print('base: rows header at', k)
    if l.startswith('theorem exists_zone'): print('base:', l[:60], 'at', k)
print('first 126 lines identical:', a[:126] == b[:126])
