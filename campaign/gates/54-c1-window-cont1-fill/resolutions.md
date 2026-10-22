# C1-WC continuation 1, the bounded input window copier (PR #137, a fill gate): resolutions (round 1; gate CLOSED)

**Gate:** the fill gate of PR #137 (`lean/c1-window-fill` at `9d8ab646`):
`Turing.exists_inputWindowCopyTM` proved in `Build/InputWindow`, a maintainer-verified fill of the
worker's repaired draft (16 private `iw_` declarations). Pack `pack.md`; bundle SHA-256
`141d6d702febba320dd1772b5eff0bbea2d2178486ceebdcd596df03a6db619e` (25 sections; folder
`54-c1-window-cont1-fill-gate/`). Replay passed (user, 2026-10-21): 2 of 2, static-equal (0).

**Round 1** (`findings.md`, verbatim; received 2026-10-21): **FAIL, 0 blockers, 1 major, 1 minor,
10 notes.** The major is a debt major. The user acknowledged it (2026-10-21), so it closes by
`TEMPLATE.md` failure mode 5 and `workflow.md` §4. **The gate is closed.** The minor is fixed on
#137 for the one line #137 changed (`fb6210b7`), with a re-replay of #137's 2-module closure
(`replay-l137b.sh`). The module docstring's inherited labels stay with the deferred documentation
cleanup. Review: `evidence/round1-review/REVIEW.md`.

| # | Severity | Finding | Resolution |
|---|---|---|---|
| 1 | major | `iw_patch` is `@wordPatch Bool`, an exact copy of a public definition already at the worker's base. The pack's "design-parallel watch item" understates it, and no human acceptance is on record. | **True; acknowledged as debt (user, 2026-10-21), as ledger IW-1 and backlog §1 IW-1.** The copy is the whole definition: token for token after renaming the binders, and `@iw_patch = @wordPatch Bool` by `rfl` (`evidence/round1-review/patch-family.txt`, `optionB/probe-axioms.out`). `StepClock` is byte-identical at the base `96d60278` and the head. The review found the same definition twice more, as `Build/CounterLoop`'s private `counterPatch` and `Build/Catalog`'s private `catalogTape`. The tree and the open branches hold no fifth copy (`patch-family-sweep.txt`, `patch-family-open-branches.txt`). **The acknowledgment covers the four as one family.** `iw_patch_append` and `iw_patch_true` are not members, since their statements differ. The first is the append form of Catalog's public `catalog_write_take`. **Census:** `InputWindow` 1 of 17 declarations (5.9%), 5 lines; `StepClock` 1 of 41; `CounterLoop` 1 of 79; `Catalog` 1 of 505. None is past one fifth. **Retirement, in the user's dedup window:** `wordPatch` moves below `Build/Catalog` with Catalog's next edit, and the three private copies re-point to it. `InputWindow`'s re-proofs are verified now (the review's option B). The pack's question-6 classification ("design-parallel watch item") is withdrawn: watch items carry no byte-copies. |
| 2 | minor | The pack says the module and facade carry no campaign labels. The module docstring still says "user decision 5 of 2026-10-13", "C1 design note", "U7" and "U-1", and the facade "C1; user decision 5 of 2026-10-13". | **True in part; erratum; the changed line fixed.** The 16 private docstrings and the module's status line carry no labels. The module docstring's labels (lines 15–16 and 20) predate #137, which leaves them untouched, so they stay with the deferred cleanup (a rewording is drafted: `evidence/round1-review/minor2/moddoc-optional.diff`). The facade's line 169 is a line #137 changed ("Sorried." → "Proved."), and it carries the label. It now reads "for the nondeterministic time hierarchy [AB09, Theorem 3.2]" (`fb6210b7`; `minor2/facade.diff`), and the facade elaborates against `oleans-l137` with 0 diagnostics. Erratum to the pack's question 7: the assertion held for the private docstrings and the status line only. |
| 7 | note | The four boundary cases follow from the branches; the bundled example output is empty. | **Done.** The records held only the empty output. The examples' source is added (`evidence/round1-review/note7/IWEdge.lean.txt`: 4 examples over the landing file). |
| 11 | note | Screens and lint hold as recorded; the screens do not establish the absence of semantic duplication. | **Done.** The pack's lint record is the tip's, before #132 was merged in (Primitives at 6,886 lines). Lint at the merged head `9d8ab646` gives the same 0 FAIL and 30 WARN over 38 files (`evidence/round1-review/lint-build-head-9d8ab646.txt`). Finding 1 covers the semantic duplication. |
| 3–6, 8–10, 12 | notes | The bundle's integrity; the repairs; the definitions and route; the contract; the constant and first arrival; the seal; rule 11 and the probes; the elaboration and replay records. | No action. Each was re-checked (`evidence/round1-review/REVIEW.md`, table): the bundle hash, its 25 sections and the replay pins; `repairs.diff` reproducing `e4228201…` at fuzz 0; `C = 6`; the four seal controls; the 57- and 84-check probes. |

**Re-replay for the minor: passed (user, 2026-10-22):** `evidence/replay-l137b.sh`, 2 of 2 at
`fb6210b7` (`Build/InputWindow` and the facade), 0 failed, static-equal (0), from `oleans-l132b`
(`evidence/replay-l137b.*`). The campaign's merges since meet this closure only at the facade.
