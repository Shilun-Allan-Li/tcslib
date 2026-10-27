# E-Q cont1, the stage query's main machine: the pre-ship on the landed tree (maintainer, 2026-10-27)

**Tree:** PR #173's head `599497bc` (E-Q checkpoint 1's landing, with the campaign after #171 merged
in), measured on a frozen detached worktree at its parent `a5c22dd9`, whose Lean is identical. The
owned file's blob is `f965eac02e06549e8239c7476b31c0ced4f3d11b` (498 lines; 22 public, 3 private).
**Snapshot:** `oleans-leqcp1`, #173's replay (2 of 2, static-equal), which is this tree.
Lean ran through `tools/leanelab.sh`, one elaboration at a time. Each `.out` is the raw output with
paths stripped; its last line gives the exit status.

**Valid while the campaign's Lean is this tree.** If #172 (H's landing) merges before cont1 issues,
`NTimeHierarchy` changes. It is in the order list and the screen population, it would import this
file (the order list must then be re-sorted: it now has `NTimeHierarchy` at 80 and
`NTimeDiagonalizer` at 83), and its one sorry would go. Re-take the order list, the base sorry set
and the screen base then.

| Check | Result | File |
|---|---|---|
| The base file | `NTimeDiagonalizer` with five axiom prints: exactly its two sorry warnings (402, the target; 472, `exists_diagonalizer`); `qy_guard`, `qy_guard_decider`, `qy_query_of_main` on the standard three. There is no overlay | `BaseFileAx.*` |
| Order list | **84 modules**, the `Diagonalization` facade's closure: the first round's 83 and `Build/WordTests`, re-sorted stably (17 positions) because #170's `CodeSimulator` imports `Build/InterpreterStartup`; import-closed and topological | `order.txt`, `stabletopo.py` |
| Roots | **34 Mathlib roots**, the first round's | `roots.txt` |
| Base sorries | **21 declarations in 10 modules**: the first round's 22 in 11 without `CodeSimulator`'s `exists_uniformSimulator` (#170) | `base-sorries.txt` |
| Import probe | 182 checks of 182 names, 0 errors, 0 warnings; identical to the first round's output | `EQImportProbe.*` |
| Route probe | 0 diagnostics, 16 axiom prints within the standard three; identical | `EQRouteProbe.*` |
| Seal controls | 7 goals: unsealed all close, sealed all fail, each at its own goal; identical | `EQSealControl.*` |
| Duplication probe | 10 of 10 "could not close"; identical | `EQDupProbe.*` |
| The review's route lemmas | 0 diagnostics, 6 axiom prints; their 5 controls fail sealed; their duplication probe 3 of 4 "could not close" (the fourth is `List.flatMap_assoc`); identical | `EQReview*.*` |
| Hosts | 47 prints with axioms, all within the standard three, none with `sorryAx`; identical | `EQHostAxioms.*` |
| Lint | `Diagonalization` 0 FAIL, 2 WARN over 5 files, the first round's WARN lines | `lint-diagonalization.txt` |
| Screen base | the 30-file population (the first round's 29 and `Build/WordTests`, which the guard cites): **1,735 declarations, 2,152 pairs, 757,579 characters**; 19 minutes under `nice -n 10`, peak memory 1.95 GB. Against the first round's base: 10 pairs gone, none new; the 10 are the twins #171 re-pointed (`a3n_`/`tmsat_` and `TMSAT_NPHard`'s two). No pair has an owned-file or `WordTests` declaration | `screen-base.*`, `screen-population.txt`, `pairdiff-vs-first-round.txt` |

"Identical" means equal to the first round's output (`preship-36cc9fc0/`) after normalizing paths,
timing lines and private-name prefixes (`cmpprobe.py`).

**For the brief.** The route probe's `qy_guard` has the statement of the landed private
`qy_guard`; the brief says to cite the landed one and not copy the probe's.
