# G4 continuation 4: the pre-ship at the campaign tip `97299639` (maintainer, 2026-10-22)

Tree: `97299639` (after #145, #146, #148). Snapshot: `oleans-lu2sc1` (#147's merged-tree replay; for
`Build/ZoneRebalance`'s closure its oleans are the tip's, since `UniversalK` and `SelfUniversal`
are not upstream of it). Every elaboration through `leanelab.sh`.

| Check | Result | File |
|---|---|---|
| Owned file | `Build/ZoneRebalance` (1,572 lines; 18 public, 73 private): the two targets' sorry warnings only (1396, 1439) | `G4C4ReturnProbe.out` (the module with one appended lemma) |
| Order list | 95 modules (continuation 3's set), 40 Mathlib roots | `order.txt`, `roots.txt` |
| Base sorries | 30 at `97299639` (continuation 3's 33, less `SeamLayout`'s 1 and `InputDevice`'s 2) | `base-sorries.txt` |
| Import probe | 448 checks of 437 names (continuation 3's worker's 445/434, `two_le_zoneStart`, `roundStop`, `not_mem_roundStop`), a standalone import: 0 errors, 0 warnings | `G4C4ImportProbe.*` |
| The return home's first premise | `g4c4_returnSkip_premise`, appended to the module: after the right pass, the outer half from the zoned head and the blank after it are `skipTM_run_ofCfg`'s word; proved from `zr_rightPass_post`, `zoneRowPre`'s tape-0 equation and `zonedTape_blank_outside`; 0 errors | `G4C4ReturnProbe.*` |
| Lint | `TuringMachine/Build`: 0 FAIL, 33 WARN over 39 files | `lint-build.txt` |
| Screen base | the 10-file population: 846 declarations, 477 pairs, 136,473 characters; no pair new or gone against continuation 3's after-screen | `screen-base.*` |

At issue: re-run all of it at the issue commit (#147, #150 and megafill A's landings move the
sorry set), and fill the draft's placeholders.
