import difflib, sys
# usage: regions.py <base> <head> : map every diff hunk (base line ranges) to the brief's regions
# (a) 143-359 home, (b) 456 the target's sorry, (c) 404-424 the status paragraph.
a = open(sys.argv[1], encoding='utf-8').read().split('\n')
b = open(sys.argv[2], encoding='utf-8').read().split('\n')
REG = {'a': (143, 359), 'b': (456, 456), 'c': (404, 424)}
def region(lo, hi):  # base lines lo..hi (1-based, inclusive); for pure insertion lo = hi+1 (insert before lo)
    for k, (s, e) in REG.items():
        if lo > hi:  # insertion before line lo: allowed if between s and e+1
            if s <= lo <= e + 1: return k
        elif s <= lo and hi <= e: return k
    return 'OUTSIDE'
sm = difflib.SequenceMatcher(None, a, b, autojunk=False)
out = 0; tot_del = tot_ins = 0
for tag, i1, i2, j1, j2 in sm.get_opcodes():
    if tag == 'equal': continue
    r = region(i1 + 1, i2)
    tot_del += i2 - i1; tot_ins += j2 - j1
    if r == 'OUTSIDE': out += 1
    print(f'{tag:7s} base {i1+1}-{i2} ({i2-i1} lines) -> head {j1+1}-{j2} ({j2-j1} lines): region {r}')
print(f'hunks outside the regions: {out}; base lines removed/replaced {tot_del}; head lines inserted {tot_ins}')
# reversal check: rebuild base from head by undoing hunks
