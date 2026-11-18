#!/usr/bin/env python3
"""Diff the FAIL and WARN line sets of two campaign_style_lint outputs (whitespace-normalized).
usage: lintdiff.py BASE HEAD"""
import sys, re
def load(p):
    s = {}
    for l in open(p, encoding='utf-8'):
        if l.startswith('FAIL') or l.startswith('WARN'):
            s[re.sub(r'\s+', ' ', l.strip())] = l.rstrip('\n')
    return s
b, h = load(sys.argv[1]), load(sys.argv[2])
for kind in ('FAIL', 'WARN'):
    bk = {k for k in b if k.startswith(kind)}; hk = {k for k in h if k.startswith(kind)}
    print(f'{kind}: base {len(bk)}, head {len(hk)}, new {len(hk - bk)}, gone {len(bk - hk)}')
    for k in sorted(hk - bk): print(f'  NEW  {h[k]}')
    for k in sorted(bk - hk): print(f'  GONE {b[k]}')
