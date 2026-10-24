"""Copy a module with the two new Seam lemmas inserted after its imports (stand-ins for the new
Seam olean), optionally followed by the phaseHostTM seal.
python3 -I mkstandin.py <seam> <in> <out> [seal]"""
import sys
seam = open(sys.argv[1], encoding='utf-8').read()
def lemma(head):
    i = seam.index(head); i = seam.rindex('\n/--', 0, i) + 1
    j = seam.index('\n\n', i)
    return seam[i:j + 1]
pre = 'namespace Turing\n' + lemma('theorem phaseHostTM_q₀ ') + '\n' + \
      lemma('theorem phaseHostTM_tr_of_red_some ') + 'end Turing\n'
if len(sys.argv) > 4: pre += '\nattribute [local irreducible] Turing.phaseHostTM\n'
src = open(sys.argv[2], encoding='utf-8').read().split('\n')
last = max(i for i, l in enumerate(src) if l.startswith('import '))
src.insert(last + 1, '\n' + pre)
open(sys.argv[3], 'w', encoding='utf-8').write('\n'.join(src))
print(pre.count('\n') + 1, 'lines inserted')
