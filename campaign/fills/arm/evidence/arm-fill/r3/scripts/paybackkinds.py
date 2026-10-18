"""The payback's 27 files, base against landed: COMMENT-ONLY (whitespace-insensitive comment-stripped
text equal) or CODE-CHANGED, with +/- lines from patch-stats.txt. usage: python3 -I paybackkinds.py <base-root> <landed-root> <patch-stats.txt>"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from leancore3 import strip_keep_lines
b, l, ps = sys.argv[1:4]
norm = lambda t: ''.join(strip_keep_lines(t).split())
k = {}
for row in open(ps, encoding='utf-8'):
    f, add, rem = row.rstrip('\n').split('\t')
    kind = 'COMMENT-ONLY' if norm(open(os.path.join(b, f), encoding='utf-8').read()) == norm(open(os.path.join(l, f), encoding='utf-8').read()) else 'CODE-CHANGED'
    k[kind] = k.get(kind, 0) + 1; print(f'{kind}\t{f}\t{add}\t{rem}')
print(k)
