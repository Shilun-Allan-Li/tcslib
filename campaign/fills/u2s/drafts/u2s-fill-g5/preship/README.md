# G5's pre-ship on #202's tree (2026-11-06)

Run at #202's head `7b5774fb` (the campaign after #196, plus `Segment.iterate_seq`), whose Lean
tree is the campaign's once #202 merges; the overlay is the scratch commit `7f05ef30` (never
pushed), which adds `import TCSlib.Complexity.TuringMachine.Build.ZoneStep` after line 8 of
`Robustness/TwoTapes.lean` (blob `cc357673` at the base). Elaborations against `oleans-lsi2`
(`replay-lsi2`'s snapshot) with `leanelab.sh`. **Re-check at issue**, on the merged tree.

| Item | Result |
|---|---|
| `OwnedFile.out`, the overlay | exit 0; one warning, `two_work_tapes_run`'s `sorry` (line 65, one line lower for the import) |
| `G5ImportProbe`, `TwoTapes`'s three imports and `Build.ZoneStep` | 213 `#check`s, 0 errors. The names are `api-check.md`'s, with its grouped rows expanded and `Segment.iterate_seq` added. Six are left out because they are outside the file by design: the target and its corollary (the file's own), `universal_TlogT` and `universalK` (downstream), and `Cfg.InWindow.apply_iff`/`mono` (`Build/CfgRecord`, not in the file's imports) |
| `Build/Embed` | already in the file's import closure, so region (a) adds only `Build.ZoneStep` |
| `order.txt`, `roots.txt` (`fillinputs.py` on the overlay) | 105 modules, 42 Mathlib roots; neither `NDNormalForm` nor `SavitchARM` is in the closure, so #191 and the deepening do not change them |
| `base-sorries.txt` | 22 entries in 9 modules, the target's included; equal, module by module, to the warnings of the snapshot chain's replay logs |
| Lint at the overlay | `campaign_style_lint.py TCSlib/Complexity/TuringMachine`: 0 FAIL, 71 WARN over 92 files; `style_lint.py` on `TwoTapes`: 0 findings |
| `screen-population.txt`, `screen-base.txt` | the draft's 21 files; the v3 screen on a `git archive` of the overlay: 1,168 declarations, 777 pairs, 272,860 characters, 0 pairs on `TwoTapes`; exit 0, 403 s |

**After the brief's review (2026-11-06; `../review/REVIEW.md`):** `Simulation` joins the screen
population (22 files), so the screen base is re-run at issue. The import probe adds
`zoneRebalanceData_eq`, `zoneExtendData_eq` (#207), `embedEmitCfg_state` and
`embedEmitCfg_output`; it is re-run at issue, on the tree with #202 and #207 merged.

**Re-run on the campaign after #202 with #207 (2026-11-06; `oleans-lzde2`, `lzde2/`):** the
import probe (217 checks, the four added names included) 0 errors; the route probe exit 0, no
output; its sealed copy 0 diagnostics; controls 33 pass unsealed, 33 fail sealed. The screen base
(`screen-base.txt`, 22 files with `Simulation`, on a `git archive` of #207's head `d01332e4` plus the
overlay's import): 1,210 declarations, 819 pairs, 281,024 characters, 0 pairs on `TwoTapes`. The
42 pairs beyond the 21-file base all have a `Simulation` declaration on one side (existing pairs
the new population member brings in); none involves `TwoTapes`.
