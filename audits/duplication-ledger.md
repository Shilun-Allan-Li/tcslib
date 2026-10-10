# Cumulative duplication ledger

The standing per-file accounting of copied proved material that
`workflow.md` §4 requires at every epoch boundary. Created as the
retrofit-R1 round-1 repair (R1-2); **rebuilt at round 2** (R2-1/R2-2 of
`audits/retrofit-r1-r2-findings.md`): the first version's arithmetic was
inconsistent (summands 261 against a printed 249), its inclusion rule was
applied asymmetrically, and it **misclassified an exact three-file copy
family as "design-harvest reimplementation"** — the round-2 auditor
proved the four relocation declarations byte-identical across `Loop`,
`Primitives`, and `Hardness` after consistent identifier substitution,
and found the 13 exact Loop-internal H3 copies omitted. This version
adopts one inclusion rule, enumerates every family, and uses the
auditor's independently computed figures wherever they exist.

## Counting convention (one rule)

**Primary rule — expanded correspondence membership**: a declaration is a
ledger member iff it belongs to a *recorded cross-declaration
correspondence* — the retrofit inventories' twin maps **including their
strengthened-counterpart rows**, the A2/F2A reports' declared copies, and
the round-2 audit's verified relocation and H3 families. Each member is
counted **once per file it inhabits**. (Secondary, where it differs: the
*strict normalized-byte-twin* count excludes the five strengthened
counterparts — Loop's `loopHost_prepare`/`loopHost_contracts`,
Primitives' `splitSolve_of_body`/`_source`/`_closed` — and H3's one
near-copy `_init` pair.) Fractions are members over the file's total
declarations. Line figures use the round-2 audit's span rule — attached
docstring and intervening closure note through the last code line,
excluding separating blank/module-note blocks — with the auditor's
computed values where available and estimates under the same rule marked
`≈`.

## State after retrofit epoch R1 (the merged PRs #9/#10)

| File | Total decls | Original-side members | Copy-side members | All members | Fraction | Lines in member blocks |
|---|---:|---:|---:|---:|---:|---:|
| `Build/Loop.lean` | 212 | 87 →Catalog (of the historical 95; strict 85) + 4 relocation originals (`emCallAction`/`emCallCfg`/`emCall_apply`/`emCall_relocate_run`, the batch-L source of the three-file family) | 13 H3 exact copies (`emLoopHost_*`; their `loopHost_*` originals are already in the 87 and are not double-counted; the `_init` near-copy noted, uncounted) | **104** | **49.1%** | 2,009 (auditor) + 73 + ≈512 |
| `Build/Primitives.lean` | 272 | 146 →Catalog (of the historical 150; strict 143) | 4 relocation copies (`emitterP2Action`/`emitterP2Cfg`/`emitterP2_apply`/`emitterP2_relocate_run` — **byte-identical to Loop's after identifier substitution**, round-2 verified) | **150** | **55.1%** | 3,162 (auditor) + 73 |
| `CookLevin/Hardness.lean` | 549 | 0 | 4 relocation copies (`clSlotAction`/`clSlotCfg`/`clSlot_apply`/`clSlot_run` — likewise byte-identical) | **4** | **0.73%** | 73 |
| `Build/Catalog.lean` | 423 | 0 | 150 Primitives-sourced + 95 Loop-sourced + 17 Wrappers-sourced (10 `f2_timed*`, 7 `catalog_redirect*`) + 2 in-file `a2_` duplicates of `f2_` sum facts | **264** | **62.4%** (strict: 259, 61.2%) | ≈6,000 |
| `Build/Wrappers.lean` | 29 (10 pub + 19 priv) | 17 | 0 | **17** | **58.6%** | ≈450 |
| `Build/Embed.lean`, `Build/Seam.lean`, `Build/VirtualInput.lean`, `Build/Zone.lean`, `Simulation.lean`, `Codes2Tape.lean` | — | 0 | 0 | 0 | 0% | 0 |

Copy-side counts deliberately include copies whose originals were deleted
in R1 (the copies persist; deletion of an original does not shrink the
copy side). The Loop inventory's recorded dispositions — the 8 dead
Loop-twin copies in Catalog (`f2_loop_silent_prefix`,
`f2_loopBody_capture`, the six `f2_loopDebit*`/`f2_loopBorrow*`) and the
orphans' dead twins — are **dispositions for 12.2c, not subtractions
here**; sole-owner/dead labels require Catalog's reference graph and are
settled at that window. Internal near-duplicates flagged by the
inventories but outside the rule (`clCountTape ≡ bufferTape`, the H3
`_init` pair) are noted, uncounted.

**Epoch R1 delta**: new copies **0**; the historical maps lost **eleven
dead originals plus one live original eliminated by replacement**
(`catalogPair_inverse`, the human-approved E1) — 245 → 233 surviving
→Catalog originals (R2-3 wording); net −1,639 lines, −83 private
declarations (76 dead + 7 replaced).

## Acknowledgment and disposition state

| Debt family | Acknowledgment | Cleanup owner and window |
|---|---|---|
| Catalog's 264 copy-side members (↔ Primitives/Loop/Wrappers + in-file) | **D-R2** (user, 2026-10-09) | the **12.2c** per-theme refactor, promoted to the next window after R1; precondition (shrunken `Build/` files) met |
| Loop's 13 H3 copies (+1 near-copy) | **D-R3** (user, 2026-10-09) commissioned the collapse mechanism — §13 Z5, **now proved** (vhost-f1) | **proposed: retrofit batch RB4** (Loop), consuming Z5, window: after the A-S1 fill gate closes — *pending explicit user acknowledgment per `workflow.md` §4* |
| The three-file relocation family (4 decls × 3 files; pre-policy legacy, disclosed at its batches as "private harvest" but verbatim in fact) | **none yet** — the round-2 audit's R2-2 requires a named owner and window | **proposed: the same RB4** (all three files), replacing the family with the R1 selected-tape exports (D-R1, proved) + Z5 agreement transfer, per the inventories' own analysis of what unlocks it — *pending explicit user acknowledgment* |

Any new copy in a future delivery enters through the per-delivery ledger
and the one-fifth escalation rule of `workflow.md` §4.
