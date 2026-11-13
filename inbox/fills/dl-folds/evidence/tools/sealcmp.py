#!/usr/bin/env python3
"""Compare whole-file seal results, base against final (dl-folds): per file and variant, the
failing declarations; a failing declaration at the final head that does not fail at the base (after
the name map for moved declarations) is NEW. usage: sealcmp.py BASE.jsonl FINAL.jsonl"""
import json, sys
def load(p):
    d = {}
    for l in open(p):
        r = json.loads(l)
        d[(r['file'], r['variant'])] = r
    return d
b, f = load(sys.argv[1]), load(sys.argv[2])
new_total = 0
for k in sorted(set(b) | set(f)):
    rb, rf = b.get(k), f.get(k)
    fb = set(rb['failing']) if rb else None
    ff = set(rf['failing']) if rf else None
    if rf is None:
        print(f'{k[0]} {k[1]}: base only (failing {sorted(fb)})'); continue
    new = sorted(ff - (fb or set()))
    gone = sorted((fb or set()) - ff)
    new_total += len(new)
    tag = 'base n/a (new file)' if rb is None else f'base {len(fb)} failing'
    print(f"{k[0]} {k[1]}: final {len(ff)} failing (exit {rf['exit']}, {rf['candidates']} candidates); {tag}; "
          f"NEW {new}; no longer failing {gone}")
print(f'TOTAL new failing declarations: {new_total}')
