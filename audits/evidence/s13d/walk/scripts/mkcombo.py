"""Concatenate the walk unit's two overlays into one elaboration probe (read-only on its inputs).

Usage: python3 -I mkcombo.py <Catalog overlay> <Contract/Catalog overlay> <out>
Contract/Catalog imports Catalog, whose overlay has no olean (none is written), so the probe is
Catalog's overlay followed by Contract/Catalog's body, importing Catalog's imports and
Contract/Basic (which does not import Catalog). Line numbers: Contract/Catalog's body starts at
the printed line.
"""
import sys
ca, cc, out = sys.argv[1:4]
a = open(ca, encoding='utf-8').read().split('\n')
b = open(cc, encoding='utf-8').read().split('\n')
CB = 'import TCSlib.Complexity.TuringMachine.Build.Contract.Basic'
assert {l for l in b if l.startswith('import ')} == {CB, 'import TCSlib.Complexity.TuringMachine.Build.Catalog'}
ia = [l for l in a if l.startswith('import ')]
out_l = ia + [CB] + [l for l in a if not l.startswith('import ')] + [l for l in b if not l.startswith('import ')]
open(out, 'w', encoding='utf-8').write('\n'.join(out_l))
print('combo:', len(out_l), 'lines; Contract/Catalog body starts at line', len(ia) + 1 + sum(1 for l in a if not l.startswith('import ')) + 1)
