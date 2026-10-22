## The rewind of a work-tape head to the start of a word (a new public row)

A new module `TuringMachine/Build/Rewind.lean`, proved:

| Declaration | What it states |
|---|---|
| `Turing.RewindPhase` | the rewind's states: `start`, `back`, `done` |
| `Turing.rewindTM k i` | one step left; left while tape `i`'s head reads a symbol; one step right at the blank, into `done` (a stationary live anchor). Nothing is written; the input head and every other tape are untouched |
| `Turing.rewindTM_run_ofCfg` | **its framed run**, in `skipBackTM_run_ofCfg`'s form. If the word `u` starts `n ≤ |u|` cells left of tape `i`'s head (the cells from relative position `-1` up to the head read `bufferTape u`), the rewind reaches `done` at exactly `n + 2` and not earlier, with the head at the word's start and nothing else changed; up to the exit that head stays within `[pos − n − 1, pos]` and every other head is fixed |

**Why** (the user's ruling, 2026-10-18: a public row first). The interpreter core's next fill
(C1-R) needs three rewinds, of the captured words and of the copied window, from just past a word
(`w` possibly empty) back to cell `0`. No published row does that: `Turing.skipBackTM` starts on
the first cell of the next field, so it needs a blank between its head and the word and a
nonempty word, and the field-layout seekers need nonempty fields. The exhaustive replay (#136)
carries a private rewind, `xr_rewindTM`, over its own state type `xr_St` (one branch of its
dispatch table); re-pointing it to this row would need a state embedding, so it is an optional
follow-up, not part of this PR.

The facade `TuringMachine` imports the module and lists it.

### Checks (maintainer, against `oleans-lc6m`, #131's replay at the merged state)

- **Elaboration:** 0 errors, 0 warnings. `rewindTM_run_ofCfg` depends on
  `[propext, Classical.choice, Quot.sound]`.
- **Rule 10:** the proof reads other files' definitions only through published lemmas
  (`step_of_tapeAction_move`, `step_of_inputMoveAction`, `Cfg.workTapeSymbols_eq`,
  `FinTM.bufferTape_nat`, `FinTM.bufferTape_left`, the run equations). With `tapeAction`,
  `inputMoveAction`, `FinTM.bufferTape`, `MultiTapeTM.step`, `MultiTapeTM.runFrom`,
  `Cfg.workTapeSymbols`, `moveInputPos` and `Action.apply` made `local irreducible`, the module
  elaborates; a control (`bufferTape u (-1) = none` by `rfl`) fails under the same seal.
- **The consumers' forms**, derived from the contract alone in the probe: R's (a word at the
  origin, the head just past it, the empty word included) and the exhaustive replay's (any head
  position `p₀ ≤ |u|`).
- **Lint:** `TuringMachine/Build` 0 FAIL, 30 WARN over 39 files (the count before the new
  module); `TuringMachine` 0 FAIL.
- **Screen (v3)**, the new module with `Build/Catalog` and the exhaustive replay as landed in #136
  (563 declarations, 416 pairs): the new module's pairs are all against `Build/Catalog`.
  - `rw_cfg` reproduces Catalog's private `catalogSeekCfg` at **100% (79 characters)**: the same
    one-line record update (set the state, move one head) over a different phase type.
    Catalog's helper is private and specific to `SeekPhase`, so it cannot be cited, and
    generalizing it would mean editing `Build/Catalog`, whose downstream is most of the library.
    **Acknowledged by the user (2026-10-18)** as duplication debt, retired in the user's dedup
    window with Catalog's next edit (one public frame over any state type, cited from both).
  - `rewindTM` against `skipBackTM`, 80% and 69%: the same table without the `gap` step, by
    design; also against `seekStartTM`, `skipTM` and `seekEndTM` (53–56%), the table pattern of
    every catalog seek.
  - No pair with the exhaustive replay's `xr_rewindTM` (its own action and state helpers).

### Replay

At the merged state: the campaign branch after #132 (`e9e97970`) was merged into this branch, with
no conflict and this PR’s files byte-unchanged. `replay-lrw2.sh`: the changed modules' downstream closure on the merged tree (2 modules: `TuringMachine/Build/Rewind`, `TuringMachine`), chained from `oleans-l132b` (#132's replay at its merged state). **Passed (user, 2026-10-21):** 2 of 2, 0 failed, static-equal (0) (`campaign/gates/55-rewind-row/evidence/replay-lrw2.*`, `campaign/gates/55-rewind-row/evidence/down-lrw2.txt`).

### Gate

A statement-and-proof gate (the API gate's form): pending.

🤖 Generated with [Claude Code](https://claude.com/claude-code)

