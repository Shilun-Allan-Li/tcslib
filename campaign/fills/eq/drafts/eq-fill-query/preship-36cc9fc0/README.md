# E-Q, the stage query: the pre-ship at the issue base (maintainer, 2026-10-27)

Tree: the campaign tip `36cc9fc0` (a records commit), whose Lean content equals #168's merge
`13120e00`; the olean snapshot is `oleans-lu2m`, #168's replay. The brief's review
(`campaign/fills/eq/reviews/brief/`) ran at `1963b3b8` (Lean after #164 and #167, `oleans-lriseqm`).
Since then #166 and #168 have merged; their Lean changes are outside the overlay's import closure,
and the owned file's blob is unchanged (`3cdc4f33`). Lean ran through `tools/leanelab.sh` against
`oleans-lu2m`, one elaboration at a time, in a worktree at the tip (`wt-eqps`, no tracked change).
Each `.out` is the raw output with paths stripped; its last line gives the exit status, the time and
the peak memory. The probes are the review's (`probe/`), each with the eighth import
`TCSlib.Complexity.TuringMachine.BufferWords` (ruling D2), and the route probe's header line
updated. **The overlay** (`NTimeDiagonalizerOverlay.lean.txt`) is the owned file with
`Mathlib.Data.Nat.Log` before line 6 and seven TCSlib imports after line 8.

| Check | Result | File |
|---|---|---|
| Owned file, base | `NTimeDiagonalizer` (361 lines; 22 public, 0 private; blob `3cdc4f33`): exactly its two sorry warnings (270, 335); 8.3 s, 1.52 GB | `elab-NTimeDiagonalizer-base.out` |
| Owned file, overlay | the eight imports: exactly the two warnings (278, 343); 1.6 s, 1.58 GB. No `Diagonalization` module in the imports' closure (the review's `out/closure.txt`) | `NTimeDiagonalizerOverlay.*` |
| Order list | **83 modules** on the overlay (the base's 81 and `Build/Contract/Catalog`, `Build/Contract/Seam`); **34 Mathlib roots** (the base's 33 and `Mathlib.Data.Nat.Log`) | `order.txt`, `roots.txt` |
| Base sorries | **22 declarations in 11 modules**, the same on the overlay as at the base | `base-sorries.txt` |
| Import probe | the review's extended probe: **182 checks of 182 names**, 0 errors, 0 warnings | `EQImportProbe.*` |
| Route probe | A1's `Complexity.timeConstructible_iff` cited (no stand-in), sealed over 7: 0 diagnostics; 16 axiom prints, all within the standard three | `EQRouteProbe.*` |
| Seal controls | 7 goals: unsealed all close; sealed all 7 fail, each at its own goal (lines 49–59) | `EQSealControl.*` |
| Duplication probe | 10 of 10 statements "could not close" | `EQDupProbe.*` |
| The review's route lemmas | `rv_release_first_stop`, `rv_call_output_nil`, `rv_seek_home`, `rv_query_word` (with `rv_flatMap_dbl_dbl`), `rv_X_cells`, `rv_cube_le`, sealed over 12 (the route probe's 7 and `Cfg.ofWords`, `stateWord`, `Cfg.mapState`, `seamReleaseTM`, `Cfg.Stopped`): 0 diagnostics; 6 axiom prints within the standard three. Their 5 extra controls: unsealed all close, sealed all 5 fail. Their duplication probe: 3 of 4 "could not close"; the fourth, doubling twice, is Mathlib's `List.flatMap_assoc` | `EQReviewProbe.*`, `EQReviewSealControl.*`, `EQReviewDupProbe.*` |
| Hosts | the 54 hosts and rows the route names: every print within the standard three (47 with axioms, 7 with none) | `EQHostAxioms.*` |
| Lint | `Diagonalization`: 0 FAIL, 2 WARN over 5 files (`EXPCOM`'s check 8, `NTimeHierarchy`'s size), the review's figures | `lint-diagonalization.txt` |
| Screen base | ⟨pending⟩ | `screen-base.*`, `screen-population.txt` |
