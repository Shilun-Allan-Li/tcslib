"""Mathlib roots of an order list in a tree (python3 -I). usage: roots.py <root> <order list>"""
import os, sys
root, order = sys.argv[1:3]
s = set()
for m in [l.strip() for l in open(order) if l.strip()]:
    for l in open(os.path.join(root, m + '.lean'), encoding='utf-8'):
        if l.startswith('import Mathlib'): s.add(l.split()[1])
print('\n'.join(sorted(s)))
