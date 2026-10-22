## Adjacent word patches join: `Turing.wordPatch_append` (a public API lemma in `Build/StepClock`)

| Declaration | What it states |
|---|---|
| `Turing.wordPatch_append` | patching `u` at `cp` and then `v` at `cp + |u|`, right after it, is patching `u ++ v` at `cp`: `wordPatch (wordPatch ct cp u) (cp + u.length) v = wordPatch ct cp (u ++ v)` |

The module's "Main definitions" list names it. No other change.

**Why** (the user's ruling of 2026-10-18 on the configuration-clock runner's escalation E2,
option B): the runner's clock writer (B6-F3, `SpaceComplexity/WindowClock`) writes the clock field
by field and must join adjacent writes into one patch. The same fact exists only as
`Build/RecordTable`'s private `rt_adjacentWrites` (with `wordPatch` unfolded), which can re-point
to this lemma in the user's dedup window. The continuation's brief issues after this lands.

The lemma and its proof are the ones the F3 review verified (`campaign/fills/b6/reviews/configclock-cont1/suggested-fix.diff`, option B), applied verbatim.

### Checks (maintainer, against `oleans-lc6m`, #131's replay at the merged state)

- **Elaboration:** `Build/StepClock` 0 errors, 0 warnings. `wordPatch_append` depends on
  `[propext, Classical.choice, Quot.sound]`.
- **Rule 10:** the proof reads `FinTM.bufferTape` only through `FinTM.bufferTape_nat`, and
  `wordPatch` only through `wordPatch_of_mem`/`_of_not_mem`. With `FinTM.bufferTape` and
  `wordPatch` made `local irreducible`, the proof elaborates; two controls (`bufferTape u (-1) =
  none` and `wordPatch ct cp [] = ct`, both by `rfl`) fail under the same seal.
- **Lint:** `TuringMachine/Build` 0 FAIL, 30 WARN over 38 files (the tip's count; `StepClock`'s
  existing size warning, now 1,205 lines, 9 public / 33 private). No new line over 100
  characters.
- **Screen (v3):** `Build/StepClock`, `Build/RecordTable`, `SpaceComplexity/WindowClock` and
  `Build/WindowRun`: 176 declarations, 19 pairs; `wordPatch_append` is in none (not even with
  `rt_adjacentWrites`).

### Replay

At the merged state: the campaign branch was merged in after #132 (`4fcb1a7f`) and after #133,
#134, #136, #138 and #140 (`1cd66f1b`), with no conflict and `Build/StepClock` byte-unchanged.
Since #136, `ClassNP/ExhaustiveReplay` imports `Build/StepClock`, so the closure meets several
merged PRs'. `replay-lwpa.sh` replays the downstream closure of every file changed since #132's
merge (14 modules, the facade last), chained from `oleans-l132b`. **Passed (user, 2026-10-22):**
14 of 14, 0 failed, static-equal (8) (`campaign/gates/56-wordpatch-append/evidence/replay-lwpa.*`).

### Gate

Gate 56 (`campaign/gates/56-wordpatch-append/`), an API gate: pending.

🤖 Generated with [Claude Code](https://claude.com/claude-code)


