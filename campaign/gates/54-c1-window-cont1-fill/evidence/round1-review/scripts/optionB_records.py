import sys
d = sys.argv[1]
led = open(f'{d}/duplication-ledger.orig.md', encoding='utf-8').read()
anchor = """`StepBlock` is under one fifth, and #140 leaves it byte-unchanged. After the retirement, neither
file has a member.
"""
entry = """
**IW-1, the interval-patch family** (found at gate 54, 2026-10-21): one definition, a tape with a
word written over an interval, in four files: `Build/Catalog`'s private `catalogTape` (written
pointwise) and `Build/CounterLoop`'s private `counterPatch`, both from 2026-10-10;
`Build/StepClock`'s public `wordPatch` (2026-10-14); and PR #137's private `iw_patch` in
`Build/InputWindow`, token for token after renaming the binders. The tree and the open branches
hold no other. **`iw_patch` was retired before landing** (gate 54, option B: `InputWindow` imports
`StepClock` and cites `wordPatch`), so #137 lands no copy. The B6 F1 record named `counterPatch`
for the dedup window; `catalogTape` was not recorded before. The copy-text screen pairs none of
them, since the identifiers differ. **ACKNOWLEDGED (user, ⟨date⟩)**, at gate 54. **Cleanup owner
and window:** the user's dedup window, through backlog §1 IW-1: the family's home moves below
`Build/Catalog` with Catalog's next edit. **Census** (the primary rule; declarations as the style
lint counts them; lines by the span rule): `Build/StepClock`, the public home, **1 of 41 (2.4%)**,
4 lines; `Build/CounterLoop` **1 of 79 (1.3%)**, 4 lines; `Build/Catalog` **1 of 505 (0.2%)**, 5
lines, in none of the correspondences behind Catalog's row above, so one member more there;
`Build/InputWindow` **0 of 17**. No file is past one fifth, and #137 adds no copy to any file.
"""
assert led.count(anchor) == 1, 'ledger anchor'
open(f'{d}/duplication-ledger.md', 'w', encoding='utf-8').write(led.replace(anchor, anchor + entry))
bl = open(f'{d}/backlog.orig.md', encoding='utf-8').read()
anchor2 = """  correction adds no member, file or family to what the ruling chose: the module and its four
  restatements.
"""
entry2 = """
### IW-1: the interval-patch family, one definition in three files (user, ⟨date⟩)

*Origin: gate 54 (PR #137), finding 1 and its review.*

`Build/StepClock`'s public `wordPatch`, `Build/CounterLoop`'s private `counterPatch` and
`Build/Catalog`'s private `catalogTape` are one definition (a tape with a word written over an
interval). The fourth copy, #137's `iw_patch`, was retired before landing: `Build/InputWindow`
cites `wordPatch`.
- **Acknowledged (user, ⟨date⟩)**, at gate 54, on condition that the retirement stays on this
  backlog.
- **Retirement, in the user's dedup window:** `CounterLoop` cannot import `StepClock`, which
  imports it, and `Catalog` lies below both. So `wordPatch` and its cell lemmas move below
  `Build/Catalog`, beside `FinTM.bufferTape` (`Simulation`, or `TuringMachine/BufferWords`,
  merged with #140), with #139's `wordPatch_append` and an explicit-form lemma. `counterPatch`
  and `catalogTape` are then deleted and their uses re-pointed; `InputWindow`'s `StepClock`
  import can then go. This edits `Build/Catalog`, so it goes with Catalog's next edit (12.2c T3 or
  MIG-1), as RW-1 does.
"""
assert bl.count(anchor2) == 1, 'backlog anchor'
open(f'{d}/backlog.md', 'w', encoding='utf-8').write(bl.replace(anchor2, anchor2 + entry2))
print('ok')
