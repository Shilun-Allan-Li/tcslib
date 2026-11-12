#!/usr/bin/env python3
"""For each `old -> new` pair of the name map, report whether the old name is gone from the final
dump, whether the new name exists there, and whether the type hashes agree (same statement up to
the elaborated type). Usage: namemap_check.py <namemap.txt> <base dump> <final dump>"""
import sys

def load(p):
    rows = {}
    for l in open(p):
        parts = [x.strip() for x in l.rstrip('\n').split(' | ')]
        if len(parts) == 6:
            rows[parts[0]] = parts
    return rows

nm, b, f = sys.argv[1], load(sys.argv[2]), load(sys.argv[3])
for l in open(nm):
    l = l.strip()
    if not l or l.startswith('#'):
        continue
    old, new = [x.strip() for x in l.split('->')]
    ob = b.get(old)
    nf = f.get(new)
    gone = 'n/a' if old == '-' else ('kept' if old in f else 'gone')
    if old == '-':
        same = 'new lemma'
    elif ob is None:
        same = 'old not in base dump'
    elif nf is None:
        same = 'external (core/Mathlib/other module)' if not new.startswith('TCSlib.Cryptography') or new not in f else 'new missing'
    else:
        same = 'same type' if ob[3] == nf[3] else 'type differs'
    print(f'{old} -> {new} | old {gone} | new {"present" if nf else "absent"} | {same}')
