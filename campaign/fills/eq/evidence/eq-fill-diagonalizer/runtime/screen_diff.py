"""Compare two v3 screen outputs (python3 -I screen_diff.py <before> <after>): the header lines and
every pair present after but not before (new duplication) or before but not after."""
import sys
def load(p):
    L = open(p, encoding='utf-8').read().split('\n')
    return L[0], {l.strip() for l in L[1:] if l.strip()}
hb, b = load(sys.argv[1]); ha, a = load(sys.argv[2])
print('before:', hb); print('after: ', ha)
new = sorted(a - b); gone = sorted(b - a)
print(f'pairs new: {len(new)}; pairs gone: {len(gone)}')
for l in new: print('  NEW ', l)
for l in gone: print('  GONE', l)
