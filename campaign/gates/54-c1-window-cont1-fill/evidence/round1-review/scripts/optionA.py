import sys
d = sys.argv[1]
led = open(f'{d}/duplication-ledger.orig.md', encoding='utf-8').read()
anchor = """`StepBlock` is under one fifth, and #140 leaves it byte-unchanged. After the retirement, neither
file has a member.
"""
entry = """
**IW-1, the window copier's interval patch** (PR #137, `Build/InputWindow`, 2026-10-21): the
private `iw_patch` is `Build/StepClock`'s public `wordPatch` at `Γ = Bool`: token for token after
renaming its binders (`tape`, `head`, `v` for `ct`, `cp`, `u`), and equal by `rfl`
(`@iw_patch = @wordPatch Bool`). One definition; no proof is copied. The same definition is also
`Build/CounterLoop`'s private `counterPatch` and `Build/Catalog`'s private `catalogTape` (written
pointwise), both from 2026-10-10; `wordPatch` (2026-10-14) is the public one. These four are the
**interval-patch family**: the tree and the open branches hold no other. The B6 F1 record named
`counterPatch` for the dedup window; `catalogTape` was not recorded before. The worker reported
"new copies: none" (`StepClock` was outside its screen population and its import context). The
maintainer disclosed the copy in gate 54's pack (question 6), and gate 54's finding 1 made it a
debt major. **Not members:** `iw_patch_append` appends one cell (Catalog's public
`catalog_write_take` states the same fact in take form, with its own proof), and `iw_patch_true`
reads the patch at the all-true word (the `Bool` case of a step inside `CounterLoop`'s proof, not
a declaration). **ACKNOWLEDGED (user, ⟨date⟩)**, at gate 54, for the whole family. **Cleanup
owner and window:** the user's dedup window, through backlog §1 IW-1: `wordPatch` moves below
`Build/Catalog` with Catalog's next edit, and the three private copies re-point to it
(`InputWindow`'s re-proofs are verified at gate 54's review). **Census** (the primary rule, each
member counted once per file it inhabits; declarations as the style lint counts them; lines by
the span rule):
- `Build/InputWindow`, a copy: **1 of 17 declarations (5.9%)** (1 public, 16 private), **5**
  lines (`iw_patch`).
- `Build/StepClock`, the public one: **1 of 41 (2.4%)** (8 public, 33 private), **4** lines
  (`wordPatch`).
- `Build/CounterLoop`: **1 of 79 (1.3%)** (59 public, 20 private), **4** lines (`counterPatch`).
- `Build/Catalog`: **1 of 505 (0.2%)** (113 public, 392 private), **5** lines (`catalogTape`). It
  is in none of the correspondences behind Catalog's row above, so it adds one member there.
- Copied characters: none by the v3 screen, which pairs none of the four. After renaming, each
  is the same definition of 175 to 199 characters.

**The one-fifth rule** (`workflow.md` §4): no file of the family is past one fifth.
`InputWindow` had no earlier copies. `Catalog` had, but #137 adds no copy to it, since
`catalogTape` predates the delivery. The §1 item IW-1 is opened anyway, as for RW-1, and
answered. After the retirement only `wordPatch` remains, in its new home.
"""
assert led.count(anchor) == 1, 'ledger anchor'
led = led.replace(anchor, anchor + entry)
open(f'{d}/duplication-ledger.md', 'w', encoding='utf-8').write(led)

bl = open(f'{d}/backlog.orig.md', encoding='utf-8').read()
anchor2 = """  correction adds no member, file or family to what the ruling chose: the module and its four
  restatements.
"""
entry2 = """
### IW-1: the window copier's interval patch, a copy of `wordPatch` (user, ⟨date⟩)

*Origin: gate 54 (PR #137, `Build/InputWindow`), finding 1; the maintainer disclosed it in the
pack.*

`Build/InputWindow`'s private `iw_patch` is `Build/StepClock`'s public `wordPatch` at `Γ = Bool`
(token for token after renaming its binders, and equal by `rfl`). The brief authorized no import,
so the worker could not cite it, and the screen pairs neither. The same definition is
`Build/CounterLoop`'s private `counterPatch` and `Build/Catalog`'s private `catalogTape`: one
definition in four files, `wordPatch` the public one.
- **Acknowledged (user, ⟨date⟩)**, at gate 54, for the whole family, on condition that the
  retirement stays on this backlog.
- **Retirement, in the user's dedup window,** in one move. `CounterLoop` cannot import
  `StepClock`, which imports it, and `Catalog` lies below both. So `wordPatch` and its cell
  lemmas move below `Build/Catalog`, beside `FinTM.bufferTape` (`Simulation`, or
  `TuringMachine/BufferWords`, merged with #140), with #139's `wordPatch_append` and an
  explicit-form lemma. `counterPatch`, `catalogTape` and `iw_patch` are then deleted and their
  uses re-pointed. `InputWindow` needs no new import, and its re-proofs are gate 54's option B
  (`iw_patch_append` and `iw_patch_true` through `wordPatch_of_mem`/`_of_not_mem`, with a private
  explicit-form reading; verified: 0 errors and 0 warnings, a seal of 19 definitions with 5
  controls, the statement unchanged). The move edits `Build/Catalog`, so it goes with Catalog's
  next edit (12.2c T3 or MIG-1), as RW-1 does. If `InputWindow` is wanted earlier, option B
  lands it alone, importing `StepClock` (acyclic; the closure gains that one module).
- **Census** (`duplication-ledger.md`, IW-1): `InputWindow` 1 of 17 declarations (5.9%),
  `StepClock` 1 of 41, `CounterLoop` 1 of 79, `Catalog` 1 of 505; none is past one fifth.
"""
assert bl.count(anchor2) == 1, 'backlog anchor'
bl = bl.replace(anchor2, anchor2 + entry2)
open(f'{d}/backlog.md', 'w', encoding='utf-8').write(bl)
print('ok')
