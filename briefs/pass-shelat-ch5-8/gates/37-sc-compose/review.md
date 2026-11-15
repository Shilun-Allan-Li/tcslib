# sc-compose · maintainer delivery review (r1)

**Verdict: ACCEPT WITH LANDING EDITS.** The landing edits are LE-doc and LE-prose. Draft [PR #324](https://github.com/Shilun-Allan-Li/tcslib/pull/324).

## Delivery and landing
- **Delivery:** a Claude worker. The final is at exchange `bdfdcb76`; the checkpoints are `419c4ceb` and `f1ba0b1a`. The issue base is `107f1e8c`.
- **Landing:** `land/pass-shelat-sc-compose`, on `6ce4658d`. The range-diff is 12/12 identical.
  - **Head:** `a6eaebd78c48e7fdfd06263edb84b70bc00ec593`.
  - **Commits:** the worker's twelve (`7c31136e` … `f3036c69`), then two landing edits:
    - LE-doc `f61ce08f`, tree `f7432799`: formulas for 70 new public declarations.
    - LE-prose `a6eaebd7` (SC-F03).
- **Files:** 16 files, +4580/−60: the owned `ComposeSecurity.lean` and 15 helpers under `ComposeSecurity/`.
- **Evidence:** `review-evidence.zip`, SHA-256 `c11ce8bb81d2ab7bf19259740f78c1dd2006d08e14e6672f9b257a131445a24b`, 851 entries.

## Checks
- **Integrity:**
  - The manifests verify 1062/1062 and 1031/1031.
  - The 12 hashes reproduce only with signing on (SC-F05).
  - `src/` equals the 16 files. The package verifies 7/7 and its sources 152/152.
- **Build:**
  - 279/279 modules give rc 0, with 0 errors in both forms, and 0 warnings in the unit's modules. The whole-tree check covers 1264 modules: OK.
  - The build ran at LE-doc `f61ce08f`. LE-prose changes only a docstring: the code is identical with doc comments stripped (maintainer check). It is rebuilt in #324's integration build.
- **Statements:** the owned file's 11 declarations show 0 differences, and each control reports exactly 1. Exactly the 3 targets change. decls2 gives 185 ADDED, 0 CHANGED, 0 REMOVED. There are 0 name clashes.
- **Axioms:** the targets and `polyTime_compose` use only the standard three. None of the 258 stored constants uses `sorryAx`.
- **Rule 10:** the seals pass 64/64 at the head and 4/4 at the base. The coe controls are ALL_OK; strict fails only on `ctlCoeReader`. The scan finds 0 foreign definitions.
- **Admissions:** 31 → 28, by exactly the three targets.
- **Lint:** 92/101, with identical line sets.
- **Content:** the proof follows the five-step sketch, with ε = ε_A + ε_B.
- **Overlap:** the trial merges with #313, #318, #319 and sc-garble are clean.
- **Restore:** `dl-oleans` is exactly `457ba704…`.

## Findings

| # | Severity | Finding | Disposition |
|---|---|---|---|
| SC-F01 | minor | Public lemmas are restated instead of imported, because the worker read the brief's two allowed imports as exhaustive. The restatements are disclosed in the checkpoint REPORTs: a third `negligible_polyExpr_mul` (`EnsemblesLemmas.lean:377`); `appendCoins` = `coinsEquiv`; `ofFn_blocks_symm` = `FunFamily.ofFn_blocks_symm`; and `polyTimeComputable_flatMap_range`, `flatMap_range_ite`, `iterSnd_poly`, `encodeMsgs_eq_flatMap`, `msgAt_encodeMsgs` and the `padTo` family from `ThreeColoring/Machines.lean`. | **Ruling (Seyoon, 2026-11-15): ledger.** DL-49; re-point in the cleanup. |
| SC-F02 | info | The final REPORT's overlap section relies on the checkpoint tables. | Copies are in the evidence. |
| SC-F03 | minor | The frozen prose of `polyTime_compose` still called the efficiency theorems `sorry`s. | **Ruling (Seyoon): a prose-only exception.** Fixed by LE-prose `a6eaebd7`; the header and code are identical. |
| SC-F04 | info | 70 public declarations had no formula. | **Fixed** by LE-doc. |
| SC-F05 | info | `COMMITS.tsv` has no signing column. | Note. |
