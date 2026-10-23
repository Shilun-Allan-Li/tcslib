# B5a, the canonizer's continuation 7: the grammar stage (PR #152, a fill gate): resolutions (round 1; PASS; gate CLOSED)

**Gate:** the fill gate of PR #152 (`lean/b5a-canon-cont7` at `8e74681a`: the delivery's 8 commits
and the maintainer's four, on the campaign branch at `86523ba5`), with the relabeling-collapse
re-point `e4c5d015` prepared for landing. Pack `pack.md`; bundle SHA-256
`8be5237bdc414ac4c02c9951c6a6a24a69b558a0af9fc7cdaf187bba94c18efa` (228 sections; folder
`67-b5a-canon-cont7-fill-gate/`), built from the Lean files at `8e74681a` and the records at
`e441cc93`. By the user's ruling (2026-10-23) it was dispatched before the post-#149 replay.

**Round 1** (`findings.md`, verbatim; received 2026-10-23, SHA-256
`af63aedb05ee837b6840d445761ac72cabd8c426f3b3aa69369ec24db297d312`): **PASS, 0 blockers, 0 majors,
3 minors, 15 notes. The gate is closed.** The maintainer checked the three minors directly: all
true as readings; minor 1 is answered by a ruling on rule 10's scope.

| # | Severity | Finding | Resolution |
|---|---|---|---|
| 1 | minor | The re-point's two `rfl`s close `g ∘ f` against the lambda by reducing core's `Function.comp`; rule 10 names no core exception (the review applied it to `Bool.toNat`), and the 36-name seal covers TCSlib definitions only. | **True as a reading; answered by a ruling, no code change.** **Ruled (user, 2026-10-23): rule 10 binds TCSlib's own definitions.** Core and Mathlib definitions may reduce in a `rfl`, `decide` or `show` step, but are never passed to `simp`, `rw` or `unfold`; their equation lemmas are used instead (the `Bool.toNat` fix was of that kind: a core definition passed to `simp`, which also created a public constant). `policy.md` and the two unissued briefs (F3 continuation 2, G4 continuation 4) now say so. The seals are described as TCSlib-only. The same `rfl` pattern in #153's NDHost sites and the UN landing's `un_step'` is within the rule. |
| 2 | minor | The new `Implementation.` paragraph says the record validator's entry and success states coincide; they are distinct, and the adapter makes a fresh-anchor first-return round. | **True; fixed.** Commit `aed162fd` on #152, docstring only: the validator has an entry and two distinct verdict ports, and `canonReturnAdapter` turns it into a positive first-return-or-escape round before it becomes the counter loop's body. The code is identical with comments stripped; the module elaborates against `oleans-lu2sc1` with only `exists_uniformSimulator`'s sorry warning (`evidence/round1-fix/`). A docstring-only change needs no gate. |
| 3 | minor | CC7-1 lacks the counting convention's member inventory, denominator, fraction and spans. | **True; ledger completed.** CC7-1's census: 11 members in three families (the two cut legs, the seven stage legs, the per-record bound pair), with IR-1's `canonGramMapComp` until the re-point: 12 of 198 declarations (6.1%), 775 lines; after the re-point 11 of 197 (5.6%), 762 lines; spans by declaration. The other new pairs are screen matches, not members. The acknowledgment and the dedup window are unchanged. |
| 6 | note | Concrete minimal-table and truncation cases would be useful permanent sanity lemmas. | **Agreed; backlog** (optional, with the canonizer's next change). |
| 10 | note | Retire the unused `canonCounterRepeat` link in the designated dedup window. | **Agreed;** already in the backlog. |
| 11 | note | Do not describe the TCSlib-only seal as excluding all core definitional reductions. | **Agreed;** consistent with the ruling in row 1. |
| 13 | note | Apply the re-point only with #153's API available. | **Agreed.** It is applied at landing once #153 has merged. |
| 17 | note | Carry the review's logging requirements into the next dispatch. | **Agreed;** they are in the backlog's list for the next cover brief. |
| 18 | note | The replay must pass on the latest merged-tree snapshot before merge, including the re-point when applicable. | **Agreed.** After #149 (and #153) merge, the campaign branch is merged into #152, the re-point is applied, and the closure replays. |
| 4, 5, 7–9, 12, 14–16 | notes | Integrity and freeze; the frozen statements; empty and huge inputs; the stage-front and grammar-host definitions; the elaboration and admission records; the acknowledged families; probes and lint; the text repairs. | No action. |

**Landing** (2026-10-23): with #147, #149, #150, #151 and #153 merged, the campaign branch merged
into #152 cleanly (`fe202202`, `274bdae9`) and the prepared re-point `e4c5d015` was cherry-picked
as `2e115bf1`. Its code equals the audited re-point's; the only difference is `aed162fd`'s
docstring (`evidence/landing/diff-vs-audited-repoint.txt`). Against `oleans-lrc2` the module
elaborates with only `exists_uniformSimulator`'s sorry warning, and `exists_polyCanonizer` is on
`[propext, Classical.choice, Quot.sound]` (`evidence/landing/`). Replay: `replay-lcanon7.sh`, the
closure of every file changed since `oleans-lrc2` (#150's `CfgRecord` with this PR's: 61 modules),
at `274bdae9`.

**Merge state. #152: not yet clear to merge.** Its replay is pending.
