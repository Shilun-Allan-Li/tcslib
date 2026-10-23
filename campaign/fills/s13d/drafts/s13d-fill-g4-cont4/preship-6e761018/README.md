# G4 continuation 4: the pre-ship at the campaign tip `6e761018` (maintainer, 2026-10-23)

Tree: `6e761018` (after #147 and #149–#155; its Lean tree equals #155's head `6efc5be0`).
Snapshot: `oleans-lslsk` (#155's replay, the same tree). Every elaboration through `leanelab.sh`.
This re-runs the pre-ship of `97299639` (`../preship-97299639/`) at the issue tree.

| Check | Result | File |
|---|---|---|
| Owned file | `Build/ZoneRebalance` unchanged since `97299639` (1,572 lines; 18 public, 73 private): with the appended `g4c4_returnSkip_premise`, the two targets' sorry warnings only (1396, 1439) | `G4C4ReturnProbe.*` |
| Order list | 96 modules: the 95 of `97299639` and `Build/InputRewind` (#153, through `Build/NDHost`); 40 Mathlib roots, unchanged | `order.txt`, `roots.txt` |
| Base sorries | 27: the 30 of `97299639` less `exists_canonGrammarStage` (#152), `exists_ndInterpreterCore` (#151) and `exists_selfStartupTMK` (#147) | `base-sorries.txt` |
| Import probe | 448 checks of 437 names, a standalone import: 0 errors, 0 warnings | `G4C4ImportProbe.*` |
| Lint | `TuringMachine/Build`: 0 FAIL, 33 WARN over 40 files (one more file than at `97299639`: `InputRewind`) | `lint-build.txt` |
| Screen base | the 10-file population: 846 declarations, 477 pairs; no pair new or gone against `97299639`'s base | `screen-base.*` |

`fillinputs.py` (here) computes the lists with `git show`; at `97299639` it reproduces that run's
roots, base sorries (as entries; their order follows the order list's) and order set.
