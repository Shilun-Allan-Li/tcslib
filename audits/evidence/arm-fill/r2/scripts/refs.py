"""Code references (comment-stripped) to names matching a regex across TCSlib, outside a given
line range of a given file. usage: python3 -I refs.py <root> <regex> <file> <lo> <hi>"""
import os, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from leancore import strip_keep_lines
root, rx, f0, lo, hi = sys.argv[1], re.compile(sys.argv[2]), sys.argv[3], int(sys.argv[4]), int(sys.argv[5])
tot = 0
for dp, dn, fn in os.walk(os.path.join(root, 'TCSlib')):
    for f in fn:
        if not f.endswith('.lean'): continue
        p = os.path.join(dp, f); rel = os.path.relpath(p, root)
        for i, line in enumerate(strip_keep_lines(open(p, encoding='utf-8').read()).split('\n'), 1):
            if rel == f0 and lo <= i <= hi: continue
            for m in rx.finditer(line):
                tot += 1; print(f'{rel}:{i}: {m.group(0)}')
print('total', tot)
