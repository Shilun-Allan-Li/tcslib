import sys, re
from collections import Counter
t = open(sys.argv[1]).read(); t1 = ' '.join(t.split())
ax = {}
for m in re.finditer(r"'([^']+)' depends on axioms: \[([^\]]*)\]", t1): ax.setdefault(m.group(1), m.group(2))
for m in re.finditer(r"'([^']+)' does not depend on any axioms", t1): ax.setdefault(m.group(1), '(none)')
srcs = re.findall(r'(Turing\.\S+): direct sorryAx users in closure: (\[[^\]]*\])', t1)
ext = re.findall(r'EXT (\S+): external (\d+) \(TCSlib (\d+)\); external privates (\[[^\]]*\]); external eqn/unfold lemmas (\[[^\]]*\])', t1)
el = re.search(r'EXTLIST total (\d+); TCSlib (\d+): #?\[([^\]]*)\]', t1)
short = lambda n: n.replace('_private.ReviewScratch.F5Axioms.0.', '')
print('distinct axiom prints:', len(ax))
print('histogram:', dict(Counter(ax.values())))
std = {'propext', 'Classical.choice', 'Quot.sound'}
bad = {short(k): v for k, v in ax.items() if v != '(none)' and not {a.strip() for a in v.split(',')} <= std}
print('outside [propext, Classical.choice, Quot.sound] (incl. sorryAx):', bad or 'none')
for k in ['Turing.exists_rulerTestTM', 'Turing.exists_rulerDeviceTM', 'Turing.exists_rulerHostTM']: print(' ', k, '->', ax.get(k))
print('sorry sources (admission walk):', srcs)
print('ext checks:', len(ext), '; with an external private:', [short(e[0]) for e in ext if e[3] != '[]'] or 'none', '; with an external eqn/unfold lemma:', [(short(e[0]), e[4]) for e in ext if e[4] != '[]'] or 'none')
if el:
    names = [x.strip() for x in el.group(3).split(',') if x.strip()]
    print('EXTLIST total', el.group(1), '; TCSlib', el.group(2))
    if len(sys.argv) > 2: open(sys.argv[2], 'w').write('\n'.join(names) + '\n')
print('per declaration:')
for k, v in ax.items(): print('  ', short(k), ':', v)
