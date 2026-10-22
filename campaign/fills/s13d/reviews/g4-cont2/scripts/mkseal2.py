import sys, re
# usage: mkseal2.py <module> <out> <sealcand file> <extra names file> <seal-list out>
# Wraps the home (from `/-- The directed position of a slot` to `/-! ### The rows -/`) in a section making
# every collected other-file definition `local irreducible`, plus failing controls inside the section and
# the same controls after it (where they must pass).
src, out, cand, extra, listout = sys.argv[1:6]
names = set()
for l in open(cand, encoding='utf-8'):
    m = re.match(r'(\S+) type=(\S+) red=(\S+) proj=(\S+) inst=(\S+) matcher=(\S+)', l.strip())
    if not m: continue
    n, typ, red, proj, inst, mat = m.groups()
    if red == 'semireducible' and proj == 'false' and mat == 'false':
        names.add(n)
for l in open(extra, encoding='utf-8'):
    l = l.strip()
    if l and not l.startswith('#'): names.add(l)
names = sorted(names)
open(listout, 'w', encoding='utf-8').write('\n'.join(names) + '\n')
L = open(src, encoding='utf-8').read().split('\n')
rows = L.index('/-! ### The rows -/')
start = next(i for i, l in enumerate(L) if l.startswith('/-- The directed position of a slot'))
controls = '''
/-- Seal control (must FAIL inside the sealed section): a contract field read by defeq. -/
example {k : ℕ} (x w : List (ZoneSym k)) (d : Cfg 2 (ZoneSym k) SeekPhase x) :
    (skipTM_contract (0 : Fin 2) x).time w d = w.length + 1 := rfl

/-- Seal control (must FAIL inside the sealed section): a zone-layer definition read by defeq. -/
example : zoneStart 0 = 2 := rfl
'''.split('\n')
L = L[:rows] + controls + ['end G4C2Seal', ''] + [c.replace('must FAIL inside', 'must PASS outside') for c in controls] + L[rows:]
L = L[:start] + ['section G4C2Seal', 'attribute [local irreducible] ' + ' '.join(names), ''] + L[start:]
open(out, 'w', encoding='utf-8').write('\n'.join(L))
print('home lines', start + 1, '..', rows, 'sealed', len(names))
