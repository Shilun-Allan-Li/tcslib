# sc-garble · maintainer delivery review (r1)

**Verdict: ACCEPT WITH LANDING EDITS.** The landing edit is LE-doc. Draft [PR #323](https://github.com/Shilun-Allan-Li/tcslib/pull/323).

## Delivery and landing
- **Delivery:** a Codex worker on Seyoon's Mac, under the host addendum. The final is at exchange `a73072f1`; the checkpoints are `8313d3d2` and `11b3b808`. The issue base is `fbd37f44`, the head of #315, which has since merged.
- **Landing:** `land/pass-shelat-sc-garble`, head `cd9a48438c2a6548fe9e246ce569be57c9df96b3`, tree `13aa553d`, on `1321b9cb`. The range-diff is 7/7 identical.
  - **Commits:** the worker's `6b23a7b1`, `69f7fc89`, `2ca68a8e`, `60c71312`, `f48ec526`, `04adb34c` and `e5cb6129`, then LE-doc `cd9a4843`.
- **Files:** 14 files, +1901/−122:
  - the five owned files;
  - `Complexity/CircuitComplexity/DAGCircuit.lean`;
  - eight helpers: `Garbling/{CoinBlocks,Probability}`, `GarblingSecurity/{CoinMarginals,NestedBounds}`, `SpecialEncryptionMulti/{SliceParser,SliceReduction}` and `SpecialEncryptionSecurity/{Pad,WrongKey}`.
- **Evidence:** `review-evidence.zip`, SHA-256 `5a121c0290969e1f7725f997b8e5683169613a62ba4db203669a74590bd0e658`, 1201 entries.

## Checks
- **Integrity:**
  - The manifests verify 1278/1278 and 1254/1254.
  - `git am` reproduces all 7 hashes unsigned. The `COMMITS.tsv` signing column reads "none".
  - `src/` equals the 14 files. The package verifies 8/8 and its sources 166/166.
  - The host checks pass: the preflight, `slots.log`, `-k 3` on every `lake` call, and no `lake build`.
- **Build:** 388/388 modules give rc 0, with 0 errors in both forms, through root `TCSlib` and both `audits/*/Checks`. The whole-tree check covers 1257 modules: OK.
- **Statements:**
  - The frozen check covers the 139 base declarations of the owned files and the 72 of DAGCircuit, and finds 0 differences.
  - `SpecialEncryptionMulti` shows exactly the six SG-1 removals and 0 CHANGED. `of_joint` changes only in its proof: four reader names and one re-wrap. Its header and docstring are byte-identical.
  - The 11 controls each report exactly 1 difference. They include the one-character control and the seventh-removal control.
  - In `Yao.lean`, only the target body, its sketch and its bullet change; the file has 970 lines.
  - decls2 gives 55 ADDED, 0 CHANGED, 0 REMOVED. The name-clash scan finds nothing, including `zipWith_xor_append_of_le`.
- **Axioms:** the seven targets, B2, `garbling_good_whp` and `of_joint` use only the standard three, across 531 constants. `yaoProtocol_hbcSecure` keeps `sorryAx` through `yaoHybrid_*` (sc-yao), `otProtocol_*` (#318) and `hbcSecure_compose`.
- **Rule 10:**
  - Seal A passes 14/14 at the head and 6/6 at the base, strict and coe.
  - Seal B has 30 errors at the head against 21 at the base. All are attributed to `PolyExpr.eval` conversions (SG-F07).
  - The coe controls are ALL_OK. The strict ones fail only on `ctlCoeReader`.
  - The scan finds 0 foreign definitions.
- **Admissions:** 32 in 15 modules → 25 in 11, by exactly the seven targets.
- **Lint:** 92/101 and 25/391, with identical line sets. Widths are ≤ 100.
- **Content:**
  - `specialScheme_multiMessageSecure` is proved directly from D4, upstream of the corollary.
  - The B1 maximization keeps the empty-set convention.
  - The Gate 27 hand-off obligations (1)–(6) are met.
  - B2 `uprob_not_good_le_of_perm` has the brief's signature and is a corollary of the stronger `uprob_not_good_le_of_uniform_data` (SG-F02).
- **Overlap:** the trial merges with #313, #318 and #319 are clean.
- **Restore:** `dl-oleans` is exactly `457ba704…`.

## Findings

| # | Severity | Finding | Disposition |
|---|---|---|---|
| SG-F01 | minor | The frozen `DAGCircuit.lean` gains `isFaninTwo_iff`, an `Iff.rfl` reader that equals the approved patch. Seyoon's approval had been recorded only in the delivery's `scope-request/`. | **Confirmed by Seyoon (2026-11-15) and recorded in the decision log.** Accepted. sc-yao's SY-3 reader is byte-identical to it. |
| SG-F02 | info, disclosed | `yaoSeed_good_whp` goes through the stronger seed-dependent bound. | Accept. |
| SG-F03 | info | There were gaps in the sketches and the `## Main results` sections. | **Fixed** by LE-doc. |
| SG-F04 | minor, undisclosed | `Garbling/CoinBlocks.lean:73–74` adds a new inline getD-of-`List.ofFn` chain, of the DL-47 class. | **Ruling (Seyoon): ledger.** DL-47 is extended; the chain is re-pointed onto the planned generic getD reader. |
| SG-F05 | info | The generic bound `uprob_not_good_distinct_le_of_uniform_data` sits in `GarblingSecurity/NestedBounds`, not under `Garbling/`. | Move it in the cleanup. |
| SG-F06 | info | Two unused-simp-argument warnings (`SliceParser:168`, `NestedBounds:89`). | Cleanup. |
| SG-F07 | info | Seal B has 9 new errors, all `PolyExpr.eval` conversions. | None. |
