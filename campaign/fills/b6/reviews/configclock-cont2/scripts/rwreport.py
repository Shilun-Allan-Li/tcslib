import json, re, sys
from collections import defaultdict
# usage: rwreport.py <calls json> <heads json> <classify output>
calls = json.load(open(sys.argv[1], encoding='utf-8')); heads = json.load(open(sys.argv[2], encoding='utf-8'))
cls = {}
for l in open(sys.argv[3], encoding='utf-8'):
    m = re.search(r'CLS (\S+) \| (\S+) \| (.+?) \| (\S+)\s*$', l)
    if m: cls.setdefault(m.group(1), []).append((m.group(2), m.group(3), m.group(4)))
def cat(n):
    if n not in cls: return 'unclassified'
    out = []
    for full, kind, md in cls[n]:
        if kind.startswith('local'): out.append('local')
        elif md in ('this', 'TCSlib.Complexity.SpaceComplexity.F3C2RevClassify'): out.append(f'own {kind}')
        elif md.startswith('TCSlib'): out.append(f'TCSlib {kind}')
        else: out.append(f'core/Mathlib {kind}')
    return ' / '.join(sorted(set(out)))
by = defaultdict(set)
for ln, tac, h, e in heads:
    by[cat(h) if h else 'term (no head ident)'].add(h or e)
print(f'rw/simp/dsimp/unfold calls in the added lines: {sum(1 for c in calls if c["tac"] not in ("show","change"))}; '
      f'rule elements: {len(heads)}; show/change: {sum(1 for c in calls if c["tac"] in ("show","change"))}')
for k in sorted(by): print(f'\n[{k}] ({len(by[k])}): {sorted(by[k])}')
flag_tcs = [(ln, tac, h) for ln, tac, h, e in heads if h and 'TCSlib def' in cat(h)]
flag_core = [(ln, tac, h) for ln, tac, h, e in heads if h and 'core/Mathlib def' in cat(h)]
print('\nFLAG other-file TCSlib definitions passed to rw/simp/dsimp/unfold:', flag_tcs)
print('FLAG core/Mathlib definitions passed to rw/simp/dsimp/unfold:', flag_core)
own_defs = sorted({h for ln, tac, h, e in heads if h and cat(h).startswith('own def')})
print('own definitions passed (allowed):', own_defs)
unf = [(c['line'], c['arg']) for c in calls if c['tac'] in ('unfold', 'delta')]
print('unfold/delta calls:', unf)
sc = defaultdict(set)
for c in calls:
    if c['tac'] in ('show', 'change'):
        for t in c['ids']:
            sc[cat(t)].add(t)
print('\nidentifiers in show/change terms, by class:')
for k in sorted(sc): print(f'  [{k}]: {sorted(sc[k])}')
bare = [(c['line'], c['tac']) for c in calls if c['tac'] in ('simp', 'simpa', 'dsimp', 'dsimp only', 'simp only') and not c['arg']]
print('\nbare simp/dsimp (default set or no lemmas):', bare)
