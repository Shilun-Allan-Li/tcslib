#!/usr/bin/env python3
"""Compare the axioms of every stored constant, base against final (dl-folds).
usage: axcmp_dlf.py BASE_AX FINAL_AX NAMEMAP
Final constants are matched to base ones by name, or through the name map (new -> old) for moved
declarations. Prints the constants whose axiom set changed, the final constants with no base
counterpart (new), and the totals; and the sorryAx users."""
import sys
def load(p):
    d = {}
    for l in open(p):
        if l.startswith('AX\t'):
            _, mod, c, ax = l.rstrip('\n').split('\t')
            d[c] = (mod, ax)
    return d
base, fin = load(sys.argv[1]), load(sys.argv[2])
rev = {}
for l in open(sys.argv[3]):
    if l.strip() and not l.startswith('#'):
        o, n = l.rstrip('\n').split('\t')
        if n != '-':
            rev.setdefault(n, o)
changed, new, same = [], [], 0
for c, (mod, ax) in sorted(fin.items()):
    b = base.get(c) or base.get(rev.get(c, ''))
    if b is None:
        new.append((c, ax))
    elif b[1] != ax:
        changed.append((c, b[1], ax))
    else:
        same += 1
print(f'final constants {len(fin)}; matched {same + len(changed)}; same axioms {same}; '
      f'changed {len(changed)}; without a base counterpart {len(new)}')
for c, a, b in changed:
    print(f'CHANGED\t{c}\t{a} -> {b}')
for c, ax in new:
    print(f'NEW\t{c}\t{ax}')
print('sorryAx users (final):', [c for c, (m, ax) in fin.items() if 'sorryAx' in ax])
print('outside {propext, Classical.choice, Quot.sound} (final):',
      [c for c, (m, ax) in fin.items()
       if any(a.strip() not in ('propext', 'Classical.choice', 'Quot.sound', '')
              for a in ax.strip('[]').split(','))])
