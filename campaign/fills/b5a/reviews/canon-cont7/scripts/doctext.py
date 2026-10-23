#!/usr/bin/env python3
"""usage: doctext.py <file> <ranges a-b,...> : comment/docstring text in the ranges, scanned for
campaign labels, paths, dates and session words; prints every hit with its line."""
import re, sys
src, ranges = sys.argv[1], sys.argv[2]
L = open(src, encoding='utf-8').read().split('\n')
keep = set()
for r in ranges.split(','):
    a, b = map(int, r.split('-')); keep.update(range(a, b + 1))
# comment mask
text = '\n'.join(L); depth = 0; i = 0; mask = []
incom = []
cur = []
line = 1
while i < len(text):
    ch = text[i]
    if text.startswith('/-', i):
        depth += 1; cur.append('/-'); i += 2; continue
    if text.startswith('-/', i) and depth > 0:
        depth -= 1; cur.append('-/'); i += 2; continue
    if depth == 0 and text.startswith('--', i):
        j = text.find('\n', i); j = len(text) if j < 0 else j
        cur.append(text[i:j]); i = j; continue
    if ch == '\n':
        incom.append(''.join(cur)); cur = []; i += 1; continue
    if depth > 0: cur.append(ch)
    i += 1
incom.append(''.join(cur))
PAT = re.compile(r'(checkpoint|\bbrief\b|\bgate\b|\bcont\d|continuation|escalat|\bfinding|route step|\brule \d|ground rule|campaign|megafill|REPORT|audit|reviewer|\bC[1-6]\b|\bR[1-3]\b|\bH[12]\b|\bB5a\b|\bMIG|\bF\d\b|20\d\d-\d\d|\bsession\b|\bfill\b|seal|amend|\bworker\b|\bmaintainer\b|campaign/|audits/|\.md\b)', re.I)
nlines = sum(1 for n in keep if incom[n-1].strip())
print(f'comment/docstring lines in range: {nlines}')
for n in sorted(keep):
    c = incom[n-1]
    for m in PAT.finditer(c):
        print(f'{n}: [{m.group(0)}] {c.strip()[:150]}')
        break
