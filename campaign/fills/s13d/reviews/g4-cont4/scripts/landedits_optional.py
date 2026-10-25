import sys
# usage: landedits_optional.py <file>  -- B1, B2: the targets' fill-plan sketches brought in line with the proofs
p = sys.argv[1]
def edit(old, new):
    t = open(p, encoding='utf-8').read()
    assert t.count(old) == 1, (old[:60], t.count(old))
    open(p, 'w', encoding='utf-8').write(t.replace(old, new))
    print('applied:', old[:50].replace('\n', ' '))
# B1: the rebalance row's sketch (column moves and the other side)
edit('''copies the track-`t` column of the zones involved to the scratch tape with the mapped copy
(`extract := zoneSlotOf t`), re-packs it there by scans, and writes it back with the mapped copy
(`merge := zoneSlotSet t`), which keeps the other tracks and needs no save and restore, since
zones are delimited words (`Turing.zonedTape_right_word`, `Turing.zonedTape_left_word`); the
mirror side is reached through a scratch ruler of the distance to home. The scratch tape is''',
'''copies the track-`t` column of the zones involved to the scratch tape with the mapped copy
(`extract := zoneSlotOf t`), cuts the copy at the new split by one-cell blanks, and writes the
pieces back with the mapped copy (`merge := zoneSlotSet t`), which keeps the other tracks and
needs no save and restore, since zones are delimited words (`Turing.zonedTape_right_word`,
`Turing.zonedTape_left_word`); the other side is reached through a unary count, on scratch, of
the zones crossed. The scratch tape is''')
# B2: the extension row's sketch (the ruler and the left side)
edit('''consecutive blanks (the separator after zone `ℓ - 1`); measure the new zone with a scratch
ruler of zone `ℓ - 1`'s length doubled (zone `ℓ` has twice its capacity; at `ℓ = 0` finite
control writes the two cells); write the inner half as all-tracks virtual blanks and the outer
half as all-`⊠` cells; return through home and do the same on the left, through a ruler of the
distance; clear the ruler and return home. Each phase is `O(2^ℓ)`.''',
'''consecutive blanks (the separator after zone `ℓ - 1`); measure each half of the new zone with a
scratch ruler copied from the last field, zone `ℓ - 1` or, at `ℓ = 0`, the home (zone `ℓ` has
twice its capacity); write the inner half as all-tracks virtual blanks and the outer half as
all-`⊠` cells; return home and do the same on the left with the same ruler; clear the ruler and
return home. Each phase is `O(2^ℓ)`.''')
t = open(p, encoding='utf-8').read()
print('max width', max(len(l) for l in t.split('\n')))
