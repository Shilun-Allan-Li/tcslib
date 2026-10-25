# U2, the `k`-tape universal machine: the pre-ship re-run at `a524c36f` (the tree after #162; maintainer, 2026-10-25)

Tree: the campaign tip `a524c36f` (a records commit), whose Lean content equals #162's merge
`5a258cc2` and its replayed head `d4759581`; the olean snapshot is `oleans-lkit2`. The previous
re-run is `../preship-079a0707/` (the tree after #161, the route probe against #161's published
names). Since then the one Lean change is #162: the startup kit `Build/InterpreterStartup` and
`NDCodeSimulator`'s re-point to it. Neither is upstream of the owned file, so the probes are those
of `079a0707`, run again here. Lean ran through `tools/leanelab.sh` against `oleans-lkit2`. Each
`.out` is the raw output with paths stripped, and its last line gives the time and the peak memory.

| Check | Result | File |
|---|---|---|
| Owned file, base | `UniversalK` unchanged (1,762 lines; 12 public, 39 private): exactly the two targets' sorry warnings (1716, 1754) | `elab-UniversalK.out` |
| Owned file, overlay | the one import `Build/Rewind`: exactly the two warnings (1717, 1755) | `UniversalKOverlay.*` |
| Order list | 97 modules: `079a0707`'s 96 and `Build/InterpreterStartup` (in the closure through the `TuringMachine` facade); the overlay's set equals the base's; 40 Mathlib roots, the same | `order.txt`, `roots.txt` |
| Base sorries | 26 declarations in 11 modules, as at `079a0707` | `base-sorries.txt` |
| Import probe | **93 checks of 93 names**, 0 errors, 0 warnings; five axiom prints within the standard three | `U2UEImportProbe.*` |
| Route probe | against the published API, sealed over 8: 0 errors, 0 warnings; four axiom prints within the standard three | `U2UERouteProbe.*` |
| Seal controls | 8 goals: all close unsealed, all 8 fail sealed (lines 59–88), as at `079a0707` | `U2UESealControl.*` |
| Screen base | the 20-file population on a frozen worktree at the tip (`wt-mc`, `a524c36f`, no tracked change): **1,057 declarations, 788 pairs, 213,847 characters**; about 6 minutes under `nice -n 10`, peak memory 3.5 GB. Against `079a0707`'s base: no new pair; 2 gone, SD-1's `ic_input_suffix` ⇄ `pairEncode_drop` both ways (#162 deleted the `NDCodeSimulator` member). The owned file's pairs are `079a0707`'s: 13 within (none at 90% or more), one across (`ss_inputRewind_run` of `Universal`'s `timedFrame_run`, 56%) | `screen-base.*`, `screen-population.txt`, `pairdiff-vs-079a0707.txt` |

**The screen** is re-run because one population file changed: #162 re-pointed `NDCodeSimulator`
(the startup privates deleted). No other population file changed since `079a0707`'s base. None
of the open PRs (#164, #165, #166) touches the population.

**At issue.** If #164 merges first, re-run the overlay, the probes and the lists:
`ClassP/TimeConstructible` and `SpaceComplexity/Basic` are upstream of the owned file, and #164
adds readings to both. If #165 merges first, re-run the lists: it removes `ZoneRebalance`'s two
sorries from the base set. The owned file's lines do not move.
