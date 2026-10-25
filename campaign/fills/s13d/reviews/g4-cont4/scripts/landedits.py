import sys
# usage: landedits.py <worktree>   -- applies A1-A3 and C1, asserting each replacement exactly once
wt = sys.argv[1]
ZR = wt + '/TCSlib/Complexity/TuringMachine/Build/ZoneRebalance.lean'
FA = wt + '/TCSlib/Complexity/TuringMachine.lean'
def edit(path, old, new, count=1):
    t = open(path, encoding='utf-8').read()
    n = t.count(old)
    assert n == count, (path, old[:60], n)
    t = t.replace(old, new)
    open(path, 'w', encoding='utf-8').write(t)
    print(f'applied ({count}x) in {path.split("/")[-1]}: {old[:50]!r}')
# A1: the module's status paragraph
edit(ZR, '''**Status: statements.** The two rows are sorried under their proof sketches (the fill plan);
everything else here is proved. These rows replace the retired binary rows
`exists_zoneShiftInTM` and `exists_zoneShiftOutTM` of `Build/Zone`.''',
'''**Status: proved.** Every declaration is proved, both rows included; their machines and
contracts are private to this module. These rows replace the retired binary rows
`exists_zoneShiftInTM` and `exists_zoneShiftOutTM` of `Build/Zone`.''')
# A2: the main results entry
edit(ZR, '''* `Turing.exists_zoneRebalanceTM`, `Turing.exists_zoneExtendTM`: the rows (sorried).''',
'''* `Turing.exists_zoneRebalanceTM`, `Turing.exists_zoneExtendTM`: the rows (proved).''')
# A3: the facade's module list
edit(FA, '''* `Build/ZoneRebalance` — the rebalance and extension rows (§13d, G4), as contracts;
  sorried for the G4 fill.''',
'''* `Build/ZoneRebalance` — the rebalance and extension rows (§13d, G4), as contracts.
  Proved.''')
# C1: cite the published `Turing.ZoneContents.ext'` instead of its private copy
edit(ZR, '''/-- Zone contents are determined by their home and their two sides' words. -/
private lemma zr_contents_ext {ℓ : ℕ} {u v : ZoneContents ℓ} (h1 : u.home = v.home)
    (h2 : u.left = v.left) (h3 : u.right = v.right) : u = v := by
  cases u
  cases v
  cases h1
  cases h2
  cases h3
  rfl

''', '')
edit(ZR, 'zr_contents_ext', "ZoneContents.ext'", count=4)
t = open(ZR, encoding='utf-8').read()
assert 'zr_contents_ext' not in t
print('max width', max(len(l) for l in t.split('\n')))
