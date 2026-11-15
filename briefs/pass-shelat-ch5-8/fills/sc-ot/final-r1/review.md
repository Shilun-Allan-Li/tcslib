# sc-ot · maintainer delivery review (r1)

**Verdict: ACCEPT WITH LANDING EDITS.** The edits are LE-doc, which adds 50 formula docstrings, and LE-reuse, which reproves one lemma from a public one. Draft [PR #318](https://github.com/Shilun-Allan-Li/tcslib/pull/318).

## Delivery and landing branch
- **Delivery.** A Claude worker proved `otProtocol_polyTime` and `otProtocol_simulators`, [PS10, Protocol 160.4, Proposition 161.5]. The final is at exchange `a8972fa063a58ad2ffbfd221d625653d34a53ee8`, and the issue base is `107f1e8c`.
- **Landing.** `land/pass-shelat-sc-ot`, head `f62a25b3eda099c9cf9371900664752e7b89007d`, tree `163be55a`. It was rebased r1 → r2 (#314) → r3 (#315) onto `a334ec2e`; every range-diff is identical.
  - **Commits.** The worker's are `8d429067`, `53969e06` and `b2e817ca`. LE-doc is `7a1fa29b` and LE-reuse is `f62a25b3`. All are signed.
- **Files.** 7 files, +2256/−40: the owned `ObliviousTransfer.lean` and six new helpers in `ObliviousTransfer/`.
- **Evidence.** `review-evidence.zip`, SHA-256 `aa3bcfc3dfa3d434904a80885c7f70b4093981abff2592ed5d1e85e34a3d2e4f`: 811 entries, the 810 manifest paths plus `SHA256SUMS`.

## Checks
- **Integrity.** The manifests verify 219/219 and 206/206. The package verifies 7/7 and its sources 159/159. `git am` reproduces the three worker hashes, but only with signing on (F-05). `src/` equals the 7 changed files.
- **Build.** The final r3 build covers 139 modules: rc 0, and 0 errors in both the `error:` and `error(` forms. The unit modules have 0 warnings. The whole-tree check covers 1250 modules: OK.
- **Statements.**
  - The frozen check finds 0 differences in headers, prose and every definition, `EnhancedHardCore` included, so G3-8 holds. Each of its 5 controls reports exactly 1 difference.
  - decls2 gives 141 ADDED, 0 CHANGED and 0 REMOVED. The only changes to existing declarations are the two targets' proofs and sketches.
- **Axioms.** The two targets and `otProtocol_hbcSecure` use only `propext`, `Classical.choice` and `Quot.sound`, and so do all 234 stored constants. `yaoProtocol_hbcSecure` keeps `sorryAx` through the admitted Yao hybrid.
- **Rule 10.** 28 seals at the head and 4 at the base pass in A and B, strict and coe, with 0 new failures. The coe controls are ALL_OK, and the strict ones are attributed (F-09). The scan finds 0 foreign definitions across 742 items.
- **Admissions.** 31 → 29, by exactly the two targets.
- **Lint.** 92/101 for Cryptography and 25/391 for Complexity, with identical line sets. All widths are ≤ 100 and every file has ≤ 1000 lines.
- **Content.** The proof matches the book.
  - Alice's side is bounded by 2δ(n) at every `n`.
  - Bob's side uses the published `tdpPredictor` around `viewDist`, together with the signed identity. `hEHC` is applied to 16 machines and the bounds are summed into one negligible ε_B.
- **Overlap.** No open PR touches a unit file, and the unit has no PR file in its 128-module closure. The trial merge with #313 is clean.
- **Restore.** `dl-oleans` is exactly `457ba704…` after every stage.

## Findings

| # | Severity | Finding | Disposition |
|---|---|---|---|
| F-01 | minor | `OT.pairSndD_nil'` restates the public `BinArith.iterate_pairSndD_nil` at `1`. It was not disclosed. | **Fixed** by LE-reuse: the proof only changes, with no new import. |
| F-02 | minor | `OT.splitLen` and `splitLen_symm_ofFn` restate the public `coinsEquiv` (used backwards) and `ofFn_coinsEquiv` (`EnsemblesLemmas.lean:141,145`). The body also matches the private ElGamal `dlc_splitEquiv`. This was not disclosed. Reuse needs a new import and a definition change. | **Ruling (Seyoon, 2026-11-15): ledger debt, disclosed.** Recorded as DL-48. The cleanup uses `(coinsEquiv h).symm`. |
| F-03 | info | 50 new public declarations had no formula in their docstring. | **Fixed** by LE-doc. |
| F-04 | info, disclosed | `OT.uprob_signedPredictor_false/_true` adapts `exists_pkPredictor`, because `pkPredictor` has no public reader. | DL-48. The worker's promotion request, with a `pkPredictor_apply` reader, is deferred. |
| F-05 | info | Signing is not recorded in `COMMITS.tsv`. | As prf-long F-03. |
| F-06 | info, disclosed | The helpers restate the owned file's definition bodies by design; the owned file proves the equalities from its readers. | None. |
| F-07 | info | There are near-relatives that were not disclosed: `GI.pairSndD_encodeMsgs` for `getD_one_eq`, and `predict_eq`. The promotion requests are `negligible_finset_sum`, `statClose_prod_of_forall`, `exec_five` and `length_runAtL_le`. | DL-48 notes. |
| F-08 | info | The worker removed another fill's worktree on its own host. | None. |
| F-09 | info | The strict `ctlCoeReader` fails when sealed, a harness effect. The worker's claim that no control can make strict fail is wrong: the strict negative `ctlCoe` fails once. | Attributed. |
