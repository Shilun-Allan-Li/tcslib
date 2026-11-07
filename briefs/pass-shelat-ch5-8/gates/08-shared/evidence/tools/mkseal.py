"""mkseal.py SRC OUT NAMESFILE: whole-file seal, inserted after the first `open` line that follows the
file's (single) outer `namespace` line (or after that line if no `open` follows directly)."""
import sys
src, out, nf = sys.argv[1:4]
names = [l.strip() for l in open(nf) if l.strip()]
L = open(src, encoding='utf-8').read().split('\n')
i = next(k for k, l in enumerate(L) if l.startswith('namespace '))
j = i + 1
while j < len(L) and not L[j].strip(): j += 1
ins = j if L[j].startswith('open ') else i
seal = ('-- S1 SEAL: the foreign TCSlib definitions collected from the elaborated terms of the touched '
        'declarations, plus matchers (PolyExpr.eval and glNeed left unsealed)')
if names:
    L.insert(ins + 1, seal + '\nattribute [local irreducible] ' + ' '.join('_root_.' + n for n in names))
open(out, 'w', encoding='utf-8').write('\n'.join(L))
print(len(names), 'names sealed after line', ins + 1)
