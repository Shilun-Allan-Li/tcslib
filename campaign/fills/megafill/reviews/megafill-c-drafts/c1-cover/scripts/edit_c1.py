import sys
p = sys.argv[1]
s = open(p, encoding='utf-8').read()
def rep(old, new):
    global s
    n = s.count(old)
    assert n == 1, (n, old[:70])
    s = s.replace(old, new)

# F6/F9: the issue-time list in the comment
rep("""`campaign/fills/c1/drafts/c1-fill-replaycanon/preship-77f1eb4f/`. Issue-time items: @ANCESTOR@,
⟨BASE⟩, ⟨IN-FLIGHT⟩, the megafill banner, and re-running the pre-ship at the issue commit. -->""",
"""`campaign/fills/c1/drafts/c1-fill-replaycanon/preship-77f1eb4f/`. Issue-time items: @ANCESTOR@,
⟨BASE⟩, ⟨IN-FLIGHT⟩, the megafill banner (item number, cover file, budget), moving this file to
`campaign/fills/c1/briefs/c1-fill-replaycanon.md` without this comment, staging the inputs (the
pre-ship README's last paragraph), and re-running the pre-ship at the issue commit. If a Lean
change lands first, re-check what it moves: under Q-B1 (A) the harvest PR re-points this file
(the blob check, every line number, the counts, the order list, and the screen population, which
then gains the new module); #156 (since its gate-69 fix) edits `Build/StepBlock` and
`CodeSimulator`, both in the screen population. -->""")

# F6: the banner
rep("""> the shared base (below), **re-bootstrap your order list**, then follow this brief. **Budget:** 3
> hours (the cover's proposal) from your branch's creation. Deliver a checkpoint zip after each
> checkpoint: the session may end at any time.""",
"""> the shared base (below), **re-bootstrap your order list**, then follow this brief. **Budget:** 3
> hours from your branch's creation; then deliver this item's zip, partial if need be, and start
> the next item. Deliver a checkpoint zip after each checkpoint: the session may end at any time.""")

# F6: if Lean never runs
rep("""  Part 2 applies. **If Lean never runs, do not draft proofs blind.**
- **Branch at exactly that commit, not at the campaign tip:**

  ```sh
  git checkout -b fill/c1-replaycanon @ANCESTOR@""",
"""  Part 2 applies. **If Lean never runs, do not draft proofs blind:** deliver the environment
  report only.
- **Branch at exactly that commit, not at the campaign tip:**

  ```sh
  git checkout -b fill/c1-replaycanon @ANCESTOR@""")

# F6: the shared logs in the zip
rep("""  - **the session's shared environment logs** (`evidence/logs/` at the clone's root: preflight,
    cache store, roots, cache fetch, manifest check), this item's bootstrap and final sweep logs
    with **each module's time and maximum memory**, and the axiom log;""",
"""  - **the session's shared environment logs** (every file under `evidence/logs/` at the clone's
    root: preflight, toolchain, re-check, cache store, roots, cache fetch, manifest and cache
    checks), this item's bootstrap and final sweep logs with **each module's time and maximum
    memory**, and the axiom log;""")

# F9: the in-flight drafting note
rep("""- **In flight, merging after your base and invisible to it:** ⟨IN-FLIGHT⟩ (at drafting: #156,
  `Build/Seam`; #135, chapter 7 onto `main`); on their own branches in this session, the other""",
"""- **In flight, merging after your base and invisible to it:** ⟨IN-FLIGHT⟩ (at review: #156,
  `Build/Seam`, and private proofs in five other files, among them `Build/StepBlock` and
  `CodeSimulator`; #135, chapter 7 onto `main`); on their own branches in this session, the other""")

# F2: the import probe count
rep("""- **The import probe** (`C1RCImportProbe.lean.txt`, a standalone import of your module, **102
  checks of 102 names**: every declaration this brief cites, TCSlib's and the core and Mathlib
  lemmas it names, and five axiom prints): 0 errors, 0 warnings. **Re-run it after your""",
"""- **The import probe** (`C1RCImportProbe.lean.txt`, a standalone import of your module, **123
  checks of 123 names**: every declaration this brief cites except the universal NDTM (checked in
  the axiom probe below), TCSlib's and the core and Mathlib lemmas it names, and five axiom
  prints): 0 errors, 0 warnings. **Re-run it after your""")

# F3: the route probe's unsealed encoders
rep("""  fewer. Its controls (`C1RCSealControl.lean.txt`, 15 `rfl`/`exact` goals): every one closes
  unsealed and fails sealed, each at its own goal.""",
"""  fewer. Its controls (`C1RCSealControl.lean.txt`, 15 `rfl`/`exact` goals): every one closes
  unsealed and fails sealed, each at its own goal. The probe also reaches `optBoolBits` and
  `optStateBits` (inside `actionBitsK_eq`) without sealing them; seal them in yours (rule 10).""")

# F2: the cited infrastructure paragraph
rep("""The probe's 102 names: the target, the bridge and the scheme's fields; the composition step""",
"""The probe's 123 names: the target, the bridge, the scheme and its fields; the composition step""")
rep("""building blocks; Mathlib's `Primrec` combinators; the core and Mathlib list and tuple lemmas the
record-level proofs read. (`Primrec.nat_sub` is used in the route probe, not listed in the
import probe.)""",
"""building blocks; Mathlib's `Primrec` combinators; the core and Mathlib list and tuple lemmas the
record-level proofs and the pitfalls read; the seal's definitions; the core
`Turing.exists_ndInterpreterCore`.""")

# F4: rule 6
rep("""6. **Imports.** Unchanged. No TCSlib import may be added; a Mathlib import only if a needed
   lemma requires it (flag it; none is expected).""",
"""6. **Imports.** Unchanged: add no import of any kind. The queue's cache holds only its 41
   Mathlib roots, and a complete proof needs no new import (checked at review). A lemma that seems
   to need one is an escalation (ground rule 4).""")

# F3: the seal list for the fill
rep("""        and extend by every one you reach: at least `codeSkipActionK`, `codeSkipRepeat`,
        `codeReadUnary`, `pairDecode`, `codeBitsNat`), and `attribute [-simp]` on any `@[simp]`""",
"""        and extend by every one you reach: at least `codeSkipActionK`, `codeSkipRepeat`,
        `codeReadUnary`, `pairDecode`, `codeBitsNat`, `optBoolBits`, `optStateBits`), and
        `attribute [-simp]` on any `@[simp]`""")

# F5: rc_widen's docstring in the recommended code
rep("""   ```lean
   private def rc_widen (r : List Bool) : List Bool :=""",
"""   ```lean
   /-- Insert the choice tape's field (no write, a right move) after a two-tape record's input
   move and work fields. -/
   private def rc_widen (r : List Bool) : List Bool :=""")

# F5: pitfalls
rep("""- `omega` with products as atoms (`ring` first). The linter needs a literal "Proof sketch" before
  every `sorry` (partial only).""",
"""- **`codeReadUnary_append` reads `List.replicate n true ++ false :: xs`:** after `unaryFin_eq`
  and `List.append_assoc` the rest is `[false] ++ body`; rewrite `List.singleton_append` first.
- **`Primrec.option_casesOn` composites:** a `have h : Primrec fun a => (o a).casesOn …` fails
  ("failed to elaborate eliminator, expected type is not available"). Let Lean infer it
  (`have h := Primrec.option_casesOn (α := …) (σ := …) ho hf hg.to₂`, with `Primrec.to₂`), then
  `h.of_eq`, `rintro` the argument, `unfold` your definition, `rcases` the discriminants and close
  by `rfl`.
- **Core definitions stay out of `rw`/`simp`** (rule 10's scope): `Function.iterate_zero_apply`,
  not `rw [Function.iterate_zero, id]`. The key list's length: `List.length_flatMap`,
  `List.map_const'`, `List.sum_replicate_nat`, and `(workReadsK 2).length = 9` by
  `workReadsK_succ` twice and `workReadsK_zero`, then `rfl`.
- `omega` with products as atoms (`ring` first). The linter needs a literal "Proof sketch" before
  every `sorry` (partial only).""")

open(p, 'w', encoding='utf-8').write(s)
print('c1 ok')
