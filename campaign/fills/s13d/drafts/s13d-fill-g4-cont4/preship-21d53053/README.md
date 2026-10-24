# G4 continuation 4: the pre-ship at the campaign tip after #156 (maintainer, 2026-10-24)

Tree: the campaign branch at `eb0ae86e` (records), whose Lean tree is #156's merge `21d53053`.
Snapshot: `oleans-lphl2` (#156's round-2 replay, the same tree). Every elaboration through
`leanelab.sh`. This re-runs the pre-ship of `6e761018` (`../preship-6e761018/`) at the issue tree,
since #156 changed six files of this item's closure, `Build/Seam` (in the screen population) among
them.

| Check | Result | File |
|---|---|---|
| Owned file | `Build/ZoneRebalance` unchanged (1,572 lines; 18 public, 73 private): with the appended `g4c4_returnSkip_premise`, the two targets' sorry warnings only (1396, 1439) | `G4C4ReturnProbe.*` |
| Order list | 96 modules, 40 Mathlib roots: unchanged | `order.txt`, `roots.txt` |
| Base sorries | 27: unchanged | `base-sorries.txt` |
| Import probe | 448 checks of 437 names, a standalone import: 0 errors, 0 warnings; output identical to `6e761018`'s | `G4C4ImportProbe.*` |
| Lint | `TuringMachine/Build`: 0 FAIL, 33 WARN over 40 files, unchanged | `lint-build.txt` |
| Screen base | the 10-file population: 847 declarations, 477 pairs, 136,473 characters (one declaration more than at `6e761018`: #156's `Turing.phaseHostTM_run_le` in `Build/Seam`); no pair new or gone | `screen-base.*`, `screen-vs-6e761018.txt` |
