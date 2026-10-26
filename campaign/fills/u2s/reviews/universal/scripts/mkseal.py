"""Insert the seal block (attributes + controls) at the top of region (b) of the head module.
mode: sealed | unsealed | extended (sealed + the two RewindPhase instances, with their controls).
Usage: mkseal.py <UniversalK.lean> <seal_block.lean> <mode> <out>"""
import sys
uk, blk, mode, out = sys.argv[1:5]
U = open(uk, encoding='utf-8').read().split('\n')
h = U.index('/-! ## U2-U: the self-application universal machine -/')
assert U.count('/-! ## U2-U: the self-application universal machine -/') == 1
assert U[h + 1] == '' and U[h + 2].startswith("/-- The startup's endpoint tapes"), U[h + 2]
B = open(blk, encoding='utf-8').read()
assert B.count('-- SEAL-ATTRIBUTES-BEGIN') == 1 and B.count('-- SEAL-ATTRIBUTES-END') == 1
if mode == 'unsealed':
    a, rest = B.split('-- SEAL-ATTRIBUTES-BEGIN')
    _, rest = rest.split('-- SEAL-ATTRIBUTES-END')
    B = a + '-- (seal attributes removed: unsealed controls)' + rest
elif mode == 'extended':
    B = B.replace('-- SEAL-EXTRA', 'attribute [local irreducible] instDecidableEqRewindPhase instFintypeRewindPhase')
    B = B.replace('-- SEAL-CONTROLS-EXTRA', '-- C30 instDecidableEqRewindPhase\nexample : decide (RewindPhase.start = RewindPhase.start) = true := rfl\n-- C31 instFintypeRewindPhase\nexample : Fintype.card RewindPhase = 3 := rfl')
else:
    assert mode == 'sealed'
lines = U[:h + 2] + B.split('\n') + U[h + 2:]
open(out, 'w', encoding='utf-8').write('\n'.join(lines))
print('wrote', out, 'block lines', len(B.split('\n')), 'inserted before line', h + 3)
