"""replaycmp.py <replay.log> <base-log>...: per module of the replay, rc/errors and the sorry count
against each base log (a module absent from a base log is reported as such)."""
import re, sys
def parse(p):
    d = {}
    for l in open(p, encoding='utf-8'):
        m = re.match(r'^(\S+) rc=(\d+) \S+ errors=(\d+) sorry=(\d+)', l)
        if m: d[m.group(1)] = (int(m.group(2)), int(m.group(3)), int(m.group(4)))
    return d
new = parse(sys.argv[1]); bases = [parse(p) for p in sys.argv[2:]]
bad = 0
for m, (rc, er, so) in new.items():
    cmp = []
    for b in bases:
        if m in b:
            cmp.append('=' if b[m][2] == so else f'≠{b[m][2]}')
            if b[m][2] != so: bad += 1
        else:
            cmp.append('absent')
    if rc or er: bad += 1
    print(f"{m}\trc={rc}\terrors={er}\tsorry={so}\tbase: {' '.join(cmp)}")
print(f"# {len(new)} modules; rc≠0, errors or sorry-count differences: {bad}")
