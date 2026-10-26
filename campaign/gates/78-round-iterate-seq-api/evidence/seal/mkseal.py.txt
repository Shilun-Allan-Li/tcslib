import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from controls import CTL, SIMPCTL
# usage: mkseal.py <seal list (82)> <head module> <outdir>
SEAL = [l.strip() for l in open(sys.argv[1]) if l.strip()]
assert len(SEAL) == 82 and set(SEAL) == set(CTL), sorted(set(SEAL) ^ set(CTL))
head, outdir = sys.argv[2], sys.argv[3]
IMPORTS = '''import TCSlib.Complexity.TuringMachine.Build.ZoneTape
import TCSlib.Complexity.TuringMachine.Build.Contract.Basic
import TCSlib.Complexity.TuringMachine.Build.Contract.Catalog
import TCSlib.Complexity.TuringMachine.Build.Contract.Seam
'''
src = open(head, encoding='utf-8').read()
assert src.startswith('/-\nCopyright') and IMPORTS in src
attrs = 'attribute [local irreducible] ' + ' '.join(SEAL) + '\n'
erase = 'attribute [-simp] Turing.Action.apply\n'
ctl = ''.join(f'/-- Control {i + 1}: closes only by unfolding `{n}`. -/\n{CTL[n]}\n\n' for i, n in enumerate(SEAL))
simpctl = f'/-- Control 83: the default simp set unfolds `Turing.Action.apply` (its `@[simp]`). -/\n{SIMPCTL}\n\n'
hdr = IMPORTS + '\nset_option autoImplicit false\nset_option relaxedAutoImplicit false\n\nnamespace Turing\n\n'
w = lambda name, txt: open(os.path.join(outdir, name), 'w', encoding='utf-8').write(txt)
# 1. controls unsealed (+ the simp control)
w('G4C4RevCtlUnsealed.lean', hdr + ctl + simpctl + 'end Turing\n')
# 2. controls all sealed, with the simp erasure
w('G4C4RevCtlSealed.lean', hdr + 'section Seal\n\n' + attrs + erase + '\n' + ctl + simpctl + 'end Seal\n\nend Turing\n')
# 3. each control alone under its own definition's seal
each = ''.join(f'section S{i + 1}\nattribute [local irreducible] {n}\n\n{CTL[n]}\n\nend S{i + 1}\n\n' for i, n in enumerate(SEAL))
w('G4C4RevCtlEach.lean', hdr + each + 'end Turing\n')
# 4. irreducible only, no simp erasure: does the default simp set still unfold Action.apply?
w('G4C4RevSimpIrredOnly.lean', hdr + 'section Seal\n\n' + attrs + '\n' + simpctl + 'end Seal\n\nend Turing\n')
# 5. the module: seal section from the first home declaration (line 127) through the rows (before the endpoint lemmas)
lines = src.split('\n')
assert lines[126].startswith('/-- Restate a contract'), lines[126]
k_end = next(i for i, l in enumerate(lines) if l.startswith("/-! ### What the rows' endpoints say"))
pre = '\n'.join(lines[:126]) + '\n'
mid = '\n'.join(lines[126:k_end]) + '\n'
post = '\n'.join(lines[k_end:])
opening = 'section G4C4RevSeal\n\n' + attrs + erase + '\n'
mod = pre + opening + ctl + simpctl + mid + 'end G4C4RevSeal\n\n' + post
w('G4C4RevSeal.lean', mod)
first = (pre + opening).count('\n') + 1
last = (pre + opening + ctl + simpctl).count('\n')
body_start = last + 1
print('sealed', len(SEAL), '; controls in G4C4RevSeal.lean lines', first, '-', last, '; body from', body_start)
open(os.path.join(outdir, 'G4C4RevSeal.lines.txt'), 'w').write(f'{first} {last}\n')
# record each control's line in the module file
pos = (pre + opening).count('\n') + 1
rows = []
for i, n in enumerate(SEAL):
    rows.append(f'{i + 1} {n} {pos + 1}')  # the example starts after its docstring line
    pos += (f'/-- Control {i + 1}: closes only by unfolding `{n}`. -/\n{CTL[n]}\n\n').count('\n')
rows.append(f'83 simp-control {pos + 1}')
open(os.path.join(outdir, 'G4C4RevSeal.controls.txt'), 'w').write('\n'.join(rows) + '\n')
