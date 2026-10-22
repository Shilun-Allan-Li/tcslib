## The rewind of a work-tape head to the start of a word (a new public row)

A new module `TuringMachine/Build/Rewind.lean`, proved:

| Declaration | What it states |
|---|---|
| `Turing.RewindPhase` | the rewind's states: `start`, `back`, `done` |
| `Turing.rewindTM k i` | one step left; left while tape `i`'s head reads a symbol; one step right at the blank, into `done` (a stationary live anchor). Nothing is written; the input head and every other tape are untouched |
| `Turing.rewindTM_run_ofCfg` | **its framed run**, in `skipBackTM_run_ofCfg`'s form. If the word `u` starts `n ≤ |u|` cells left of tape `i`'s head (the cells from relative position `-1` up to the head read `bufferTape u`), the rewind reaches `done` at exactly `n + 2` and not earlier, with the head at the word's start and nothing else changed; up to the exit that head stays within `[pos − n − 1, pos]` and every other head is fixed |

**Why** (the user's ruling, 2026-10-18: a public row first). The interpreter core's next fill
(C1-R) needs three rewinds, of the captured words and of the copied window, from just past a word
(`w` possibly empty) back to cell `0`. No published row does that. `Turing.skipBackTM_run_ofCfg`
is for a word, possibly empty, that ends one blank before the head: skip back takes two
unconditional left steps before the same left pass, where the rewind takes one, and from cell
`0` it stops at cell `-1`, so it misses the empty word. `Turing.seekStartTM` needs a nonblank
cell under its head and nonempty fields. The exhaustive replay (#136)
carries a private rewind, `xr_rewindTM`, over its own state type `xr_St` (one branch of its
dispatch table); re-pointing it to this row is a recorded follow-up, not part of this PR.

The facade `TuringMachine` imports the module and lists it.

**Commits:** `684f3d88` (the module and the facade line); the campaign branch after #132
merged in; `24290ceb`, docstring only (gate 55, minor 2): the module header states skip back's
precondition exactly, as in the paragraph above.

### Checks (maintainer, against `oleans-lc6m`, #131's replay at the merged state)

- **Elaboration:** 0 errors, 0 warnings. `rewindTM_run_ofCfg` depends on
  `[propext, Classical.choice, Quot.sound]`.
- **Rule 10:** the proof reads other files' definitions only through published lemmas
  (`step_of_tapeAction_move`, `moveInputPos_zero`, `Cfg.workTapeSymbols_eq`,
  `FinTM.bufferTape_nat`, `FinTM.bufferTape_left`, `MultiTapeTM.runFrom_zero`,
  `MultiTapeTM.runFrom_succ_eq_step'`). With `tapeAction`, `inputMoveAction`,
  `FinTM.bufferTape`, `MultiTapeTM.step`, `MultiTapeTM.runFrom`, `Cfg.workTapeSymbols`,
  `Cfg.inputSymbol`, `moveInputPos` and `Action.apply` made `local irreducible`, and
  `Action.apply`'s simp unfolding erased, the module and both consumers' forms elaborate; the
  simp trace lists only this file's `rewindTM` and frame, local definitions and hypotheses,
  published lemmas and core or Mathlib lemmas. Ten controls, one per sealed definition and one
  for the simp unfolding, hold unsealed and fail under the same seal.
- **The consumers' forms**, derived from the contract alone, inside the seal: R's (a word at the
  origin, the head just past it, the empty word included) and the exhaustive replay's (any head
  position `p₀ ≤ |u|`).
- **Lint:** `TuringMachine/Build` 0 FAIL, 30 WARN over 39 files, the new module included
  (it adds no warning: 30 over 38 before it); `TuringMachine` 0 FAIL, 63 WARN over 81 files
  (63 over 80 before it).
- **Screen (v3)**, the new module with `Build/Catalog` and the exhaustive replay as landed in #136
  (563 declarations, 416 pairs): the new module's pairs are all against `Build/Catalog`.
  - `rw_cfg` reproduces Catalog's private `catalogSeekCfg` at **100% (79 characters)**: the same
    one-line record update (set the state, move one head) over a different phase type.
    Catalog's helper is private and specific to `SeekPhase`, so it cannot be cited, and
    generalizing it would mean editing `Build/Catalog`, whose downstream is most of the library.
    **Acknowledged by the user (2026-10-18)** as duplication debt, retired in the user's dedup
    window with Catalog's next edit (one public frame over any state type, cited from both).
  - `rewindTM` against `skipBackTM`, 80% and 69%: one 140-character block, `skipBackTM`'s
    table without its first row; also against `seekStartTM`, `skipTM` and `seekEndTM` (53–56%),
    inside the same block. Cross-file, so `rewindTM` is a ledger member as well: the module has
    2 members of 5 declarations (40%). **Acknowledged by the user (2026-10-21)** as
    the same debt, RW-1, widened: one back-pass run in Catalog's next edit, the rewind becoming
    skip back entered at `gap`.
  - `rewindTM_run_ofCfg` against Catalog's private `a2_mapSetup_run`, 52%: the run-by-induction
    idiom (`| succ t ih => rw [MultiTapeTM.runFrom_succ_eq_step', ih …`), which reaches half of
    12 short run proofs across 10 files. **Not counted, by the user's exception (2026-10-21).**
  - No pair with the exhaustive replay's `xr_rewindTM` (its own action and state helpers).

### Replay

At the merged state: the campaign branch after #132 (`e9e97970`) was merged into this branch, with
no conflict and this PR’s files byte-unchanged. `replay-lrw2.sh`: the changed modules' downstream closure on the merged tree (2 modules: `TuringMachine/Build/Rewind`, `TuringMachine`), chained from `oleans-l132b` (#132's replay at its merged state). **Passed (user, 2026-10-21):** 2 of 2, 0 failed, static-equal (0) (`campaign/gates/55-rewind-row/evidence/replay-lrw2.*`, `campaign/gates/55-rewind-row/evidence/down-lrw2.txt`).

After `24290ceb` (docstring only; the same 2 modules): `replay-lrw2b.sh`, chained from
`oleans-l132b`, pinning blob `1d1acb3f`. **Passed (user, 2026-10-21):** 2 of 2, 0 failed,
static-equal (0) (`campaign/gates/55-rewind-row/evidence/replay-lrw2b.*`).

### Gate

Gate 55 (`campaign/gates/55-rewind-row/`): **FAIL, 0 blockers, 1 major, 3 minors, 8 notes;
closed in round 1.** The major (the census under the ledger's rule) closed on the user's
acknowledgment (2026-10-21): RW-1 widened to the table at 40%, retired by unification with skip
back in the user's dedup window. Minor 2 is fixed by `24290ceb`; minors 3 and 4 are records.

🤖 Generated with [Claude Code](https://claude.com/claude-code)

