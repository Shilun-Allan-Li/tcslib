# canonizer · maintainer delivery review (r1)

**Verdict: ACCEPT WITH LANDING EDITS.** The landing edit is LE-doc, one formula docstring. Draft [PR #319](https://github.com/Shilun-Allan-Li/tcslib/pull/319).

## Delivery and landing branch
- **Delivery.** A Claude worker proved `exists_canonizerExp` (`Asymptotic/Universal.lean`), using the two `rfl` readers that Seyoon pre-approved on 2026-11-14. The exchange is at `27ae588d` and the issue base is `107f1e8c`.
- **Landing.** `land/pass-shelat-canonizer`, head `6421ac1631ef08feed297c810f0839b178d2a2bb`, tree `3e16398e`. It was rebased r1 → r3 onto `a334ec2e`; the range-diffs are identical.
  - **Commits.** `523d98cc` (the readers), `11b24a7e` (the proof) and `6421ac16` (LE-doc). All are signed.
- **Files.** 4 files, +133/−28: `CodeFormat.lean` and `CodeSimulator.lean`, one reader each; `Universal.lean`; and the new `Universal/Canonizer.lean`.
- **Evidence.** `review-evidence.zip`, SHA-256 `2b52982fd2699afa5ad38ff4ee1eb4172bbd16396619df2674f6e2c1348c00ea`. It has 839 entries.

## Checks
- **Integrity.** The manifests verify 169/169 and 160/160. The package verifies 7/7 and its sources 183/183. `git am` reproduces both hashes, but only with signing on.
- **Readers.** There are exactly the two approved ones. Each is a pure addition with the approved statement, proved by `rfl` and placed beside its definition. Each has a formula docstring, no attribute, and `List Bool` on both sides. The frozen check finds 0 other differences in `CodeFormat` and `CodeSimulator`.
- **Build.** The final r3 build covers 191 modules, rc 0 and 0 errors: the full downstream of `CodeFormat` and `CodeSimulator`, through `TCSlib` and both `audits/*/Checks`. The whole-tree check covers 1245 modules: OK.
- **Statements.** decls2 gives 4 ADDED and 0 CHANGED. The frozen check finds only the target's prose, which the brief requires, and the C-F01 whitespace. `Universal.lean` has 955 lines.
- **Axioms.** `exists_canonizerExp` uses only the standard three, and so do all 1077 stored constants. Its dependency closure (8151 constants) contains `computesFunInTime_appendBit`, `exists_polyCanonizer` and both readers. It contains neither the admitted `appendBitTM_computes` nor `sorryAx`.
- **Rule 10.**
  - The new helper passes every seal variant. `Universal` fails exactly as it does at the base. `CodeFormat`'s only new failure is the reader (C-F06), and `CodeSimulator`'s full file equals the base (C-F02).
  - Under the helper's seal, the `rfl` forms of both reader statements fail exactly once while the readers pass. So each reader is needed and sufficient.
  - The scan finds 0 foreign definitions in the touched declarations.
- **Admissions.** 19 → 18.
- **Lint.** Cryptography 92/101, unchanged. Complexity 25/391, which differs by exactly the three disclosed changes.
- **Content.** The target is `⟨c, d, d, h⟩`. The helper transports `exists_polyCanonizer` along the readers and proves `d(k+1)^d ≤ d·2^{dk}`. The edge cases `k = 0`, `d = 0` and malformed codes are covered.
- **Overlap.** No open PR touches a unit file. The trial merges with #313 and with sc-ot are clean.
- **Restore.** `dl-oleans` is exactly `457ba704…`.

## Findings

| # | Severity | Finding | Disposition |
|---|---|---|---|
| C-F01 | minor, disclosed | Six pre-existing lines over 100 characters were re-wrapped. This changes the header bytes of `length_univArg` and of the private `exists_preimage_of_fUniversal_eq`. The change is whitespace only. | Accepted as an LE-width-class change. |
| C-F02 | info | The whole-file `CodeSimulator` seals stopped at Lean's default `maxErrors` of 100. | Closed: full runs with `-DmaxErrors=0` give 177 errors in the same 58 pre-existing declarations at both the base and the head. Future seal runners pass `-DmaxErrors=0` and check the EOF record. |
| C-F03 | info | `exists_codeCanonizer` had no formula docstring. | **Fixed** by LE-doc. |
| C-F04 | info | Signing is not recorded in `COMMITS.tsv`. | As sc-ot F-05. |
| C-F05 | info | The inline bound has near-relatives that were not disclosed, `expPoly_poly` and `succ_pow_le`; neither is a restatement. | Note. |
| C-F06 | info | When sealed, the new `CodeFormat` reader fails as a cascade of `oneTapeFormat`'s `rfl` fields. Its siblings fail the same way at the base. | Attributed. |
| C-F07 | info | The worker removed another fill's worktree on its own host. | None. |
