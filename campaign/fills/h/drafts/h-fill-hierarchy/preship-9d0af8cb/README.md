# H, the nondeterministic time hierarchy: the pre-ship on the tree after #169 (maintainer, 2026-10-27)

Tree: #169's merged head `9d0af8cb`, whose TCSlib tree equals the campaign's after #169's merge
`94296486`; the snapshot is `oleans-laplusm`. Lean ran through `tools/leanelab.sh` against it,
one elaboration at a time, in the worktree `wt-b5aps` (no tracked change). Each `.out` is raw with
paths stripped; its last line gives the exit status, time and peak memory. **The overlay**
(`NTimeHierarchyOverlay.lean.txt`) is the owned file with
`import TCSlib.Complexity.Diagonalization.NTimeDiagonalizer` after line 16.

| Check | Result | File |
|---|---|---|
| Owned file, base | `NTimeHierarchy` (1,793 lines; 5 public, 10 private by the lint's count; blob `a99d95db`): exactly the target's sorry warning (1723); 11 s, 1.80 GB | `elab-NTimeHierarchy-base.out` |
| Owned file, overlay | one import: exactly the target's warning (1724); 4.2 s, 1.78 GB. No cycle: `NTimeDiagonalizer`'s closure does not contain the owned file | `NTimeHierarchyOverlay.*` |
| Order list | **81 modules**, 33 Mathlib roots: the base's set (the `Diagonalization` facade already brought `NTimeDiagonalizer` in), with `NTimeDiagonalizer` now before the owned file | `order.txt`, `roots.txt` |
| Base sorries | **22 declarations in 11 modules**, the same on the overlay; among them `exists_queryTM` and `exists_diagonalizer` (`NTimeDiagonalizer`) and `exists_codeNDTM_accepts_linear` (`ClassNP/NDNormalForm`), which H cites as statements | `base-sorries.txt` |
| Import probe | **48 checks of 48 names**, 0 errors, 0 warnings; 4 axiom prints within the standard three | `HImportProbe.*` |
| Route probe | sealed over 4 (`NTIME`, `FinNDTM.DecidesInTime`, `FinNDTM.AcceptsWithin`, `NDTM.HaltsWithin`): `nh_chain` (the chain's induction), `nh_absorb` and `nh_inclusion` (the finite absorption and the inclusion half, complete), `nh_top`, `nh_bottom`, `nh_middle` (the three thresholds' arithmetic) and `nh_stage` (a late stage of a code): 0 diagnostics after one fix (`nh_middle`'s `nlinarith` replaced by a ring identity); every print within the standard three | `HRouteProbe.*` |
| Seal controls | 4 goals: unsealed all close; sealed all 4 fail, each at its own goal (lines 42–58) | `HSealControl.*` |
| Duplication probe | the route probe's four generic statements (the chain, the absorption, the inclusion, the top threshold) posed to `exact?`: 4 of 4 "could not close". The nearest cousin, `TimeHierarchy/Separation`'s `eventually_poly_le_two_pow`, is outside the owned file's closure and of another shape | `HDupProbe.*` |
| Screen base | the 11-file population (`screen-population.txt`): **102 declarations, 6 pairs, 1,814 characters**; 4 s, 0.75 GB. The owned file has no pair | `screen-base.*` |
| Lint | `Diagonalization`: 0 FAIL, 2 WARN over 5 files (`EXPCOM`'s check 8, the owned file's size) | `lint-diagonalization.txt` |

**What the route probe settles:** the inclusion half is proved outright (`nh_inclusion`), and the
strictness half's arithmetic is proved; what remains for the fill is the chain's assembly over
`exists_diagonalizer`'s clauses and the normal form's transfers (checkpoints 2–5).
