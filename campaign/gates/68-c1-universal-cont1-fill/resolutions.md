# C1, UN continuation 1: the universal NDTM's setup (the UN landing, a fill gate): resolutions (round 1; PASS; gate CLOSED)

**Gate:** the fill gate of the UN landing: three commits prepared on the local branch
`lean/un-cont1-landing` on #153's head `ac5ce7bc` (`9031f1cf`, `34568b28`, `3ed7b854`; the PR opens
after #153 merges). Pack `pack.md`; bundle SHA-256
`46f4f053be9645cea14c1c215c1af460809fa3d0400bc03107a8ec96c3f6e970` (192 sections; folder
`68-c1-universal-cont1-fill-gate/`), built from the Lean files at `3ed7b854` and the records at
`d6b2ed92`. By the user's ruling (2026-10-23) it was dispatched before the merged-tree replay.

**Round 1** (`findings.md`, verbatim; received 2026-10-23, SHA-256
`4ae8403ae68f0df5563c54cee4ecb45325bacc76da24b237ba61b4fddf030afb`): **PASS, 0 blockers, 0 majors,
3 minors, 10 notes. The gate is closed.** The maintainer checked the three minors directly: all true.

| # | Severity | Finding | Resolution |
|---|---|---|---|
| 1 | minor | `un_bankTM`'s and `un_bank_run`'s docstrings promise the guide's word is kept without saying the guide is outside the selected bank; the run theorem correctly assumes `g ∉ S`. | **True; fixed.** A fourth landing commit, `2d380224`, docstrings only: the machine's docstring keeps the guide's word only when the guide is not a selected tape; the run's opens with a guide outside the selected bank. |
| 2 | minor | The setup pieces' header still says "the two leaf machines with their framed runs" after the re-point. | **True; fixed** in `2d380224`: the header names the guided bank-erase leaf with its framed run and the imported input rewind (`Turing.inputRewindTM`); its paragraph is reflowed. The code is identical to `3ed7b854`'s with comments stripped; the file, checked as before after the new module's text, has only `ntime_hierarchy`'s sorry warning; lint 0 FAIL, the same size warning (`campaign/fills/c1/evidence/c1-universal-cont1-landing/`: `docfix.py`, `elab-UNCat-docfix.out`, `lint-diag-final.txt`, `patches/0004-…`). A docstring-only change needs no gate. |
| 3 | minor | Two numbers: each simp trace has 139 rewrite entries, not 130; the final blob has 1,813 lines, not the lint record's 1,812. | **True; errata.** The review's "130/130" (`reviews/universal-cont1/out/52-land-simp-route-diff.txt`) undercounts: each trace has 139 entries, and the two traces are identical, which is the substantive claim. The lint record's 1,812 lines predates the maintainer's wrap of `hfin`'s type line, the last edit before `3ed7b854`, which has 1,813 lines; `2d380224` has 1,814. The historical logs stay as they are. |
| 7 | note | The proved-modulo claim is supported; after #151, report the target's chain against the merged tree. | **Agreed.** At landing, the axiom walk is re-run on the merged tree. |
| 13 | note | The merged-tree replay remains mandatory before merge. | **Agreed.** After #149 and #153 merge, the landing's four commits go onto the campaign branch in a PR, and its closure (`Diagonalization/NTimeHierarchy`, the `Diagonalization` facade) replays from the latest merged-tree snapshot. |
| 4–6, 8–12 | notes | Integrity and scope; the frozen contract and both budgets; boundary cases; rule 10; the exact re-point; the bank-erase refinement; the screen (the 88% pair is the accepted idiom); the verification records. | No action. |

**The PR: #154** (`lean/un-cont1-landing`, opened 2026-10-23 after #153 merged). The four
commits rebased unchanged onto the campaign branch at `e2f08f53` (after #147, #149, #150 and #153):
`bc933326`, `b9e4d908`, `7c65b4fb`, `1cd82e07` (were `9031f1cf`, `34568b28`, `3ed7b854`, `2d380224`;
the worker's authorship kept on the first); the final file is `2d380224`'s blob.

**Merge state. #154: not yet clear to merge.** Its closure overlaps #151's and #152's beyond the
facade, so it replays after both merge, from #152's merged-tree snapshot.
