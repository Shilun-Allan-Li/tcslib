# E-Q cont1, the stage query's main machine: the pre-ship at the issue tree (maintainer, 2026-10-27)

**Tree:** #172's merged head `940671e0` (H's landing on the tree after #173), measured on a
frozen detached worktree at that commit, with no tracked change. The campaign's Lean after #172's
merge (`b1a0aa27`) is this tree exactly. The owned file is unchanged since checkpoint 1's landing:
blob `f965eac02e06549e8239c7476b31c0ced4f3d11b`, 498 lines. **Snapshot:** `oleans-lhh`, #172's
replay (2 of 2, static-equal). It differs from `oleans-leqcp1`, #173's snapshot, in
`NTimeHierarchy.olean` alone (`olean-diff.txt`). Lean ran through `tools/leanelab.sh`, one
elaboration at a time. This folder supersedes `../preship-599497bc/` for the issue, which stays as
the record of checkpoint 1's tree.

| Check | Result | File |
|---|---|---|
| The base file | `../preship-599497bc/BaseFileAx.lean.txt`, unchanged: exit 0, exactly its two sorry warnings (402, the target; 472, `exists_diagonalizer`); `qy_guard`, `qy_guard_decider` and `qy_query_of_main` on the standard three. The output is the earlier run's, up to the printer's line wrapping of a longer private prefix (`cmpprobe.py`). 8.6 s | `BaseFileAx.*` |
| Import probe | the cont1 review's extended probe (`../review-inputs/EQImportProbe.lean.txt`): **216 checks of 216 names**, 0 errors, 0 warnings; the same output as the review's run against `oleans-leqcp1`. 2.0 s | `EQImportProbe.*` |
| The other probes | Not re-run: they ran on checkpoint 1's tree (the first round's eight in `../preship-599497bc/`, the cont1 review's three in `campaign/fills/eq/reviews/cont1-brief/out/`). No probe imports `NTimeHierarchy`, and every other olean is byte-identical between the two snapshots | `olean-diff.txt` |
| Order list | **84 modules**, the earlier list re-sorted stably over this tree's imports (`../preship-599497bc/stabletopo.py`): `NTimeHierarchy` moves from 80 to 83, after `NTimeDiagonalizer` (82), which it now imports; 4 positions change. The same set as `fillinputs.py`'s closure at `940671e0` | `order.txt`, `order-vs-599497bc.txt` |
| Roots | **34 Mathlib roots**, unchanged | `roots.txt` |
| Base sorries | **20 declarations in 9 modules**: the earlier 21 in 10 without `NTimeHierarchy`'s `ntime_hierarchy` (#172) | `base-sorries.txt` |
| Lint | `Diagonalization` 0 FAIL, 2 WARN over 5 files; only `NTimeHierarchy`'s size lines change (1,793 → 1,940 lines; 10 → 20 private) | `lint-diagonalization.txt` |
| Screen base | the **32-file population** (the earlier 30 and the machine model's `Configuration` and `Deterministic`, which the leaves cite; the cont1 review's F13): **1,781 declarations, 2,165 pairs, 758,766 characters**; 19 minutes under `nice -n 10`, peak memory 1.96 GB. Against the earlier base: 13 pairs new, none gone. 11 are inside or between the two added files (6 in `Configuration`, 4 in `Deterministic`, 1 `Deterministic` → `Catalog`). The other 2 are #172's, disclosed at gate 84: `nh_accepts_of_halts` reproduces `Nondeterminism`'s `acceptsWithin_iff_of_halts` at 61% (TR-1, ledgered) and `nh_fold` reproduces `nh_mem_of_accepts` at 50%. No pair has an owned-file declaration | `screen-base.*`, `screen-population.txt`, `pairdiff-vs-599497bc.txt` |
