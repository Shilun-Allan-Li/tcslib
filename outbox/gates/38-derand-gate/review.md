# derand (issued-r2) · maintainer delivery review (r1)

**Verdict: REVISE on F-01, then accepted under Seyoon's ruling (2026-11-16): "debt now, fix after".** No landing edit has
been made yet. F-04, a docstring LE-doc, is pending. Draft [PR #326](https://github.com/Shilun-Allan-Li/tcslib/pull/326).

## Delivery and landing
- **Delivery.** Codex on Seyoon's Mac. The final is exchange `186ffb99`; the checkpoints are `d90a0363` and `aa23fc19`. The issue base is `01de2d8b`.
- **Landing.** `land/pass-shelat-derand`, head `941b5a1e5116b1ecf3afa56188abd88159389600`, tree `ee97571a`, on `6ce4658d`. The range-diff is 4/4 identical.
  - **Commits:** `255f3e48` (checkpoint 1), `09f32f0b` (Theorem 180.1), `4afde165` (the host) and `941b5a1e` (the final).
- **Files.** 15 files, +1741/−36.
  - **Modified:** `ClassP/DTIME.lean`, `Randomized/Build/IterateFind.lean`, `Randomized/Classes.lean`, `Randomized/SeedMajority.lean` and `Randomness/Derandomization.lean`.
  - **New:** `SeedMajority/{Words,State,Enumeration,Envelope}` and `Derandomization/{RootSchedule,AdviceGap,Expanded,CoinGap,Majority,TimeBound}`.
- **Evidence.** `review-evidence.zip`, SHA-256 `ef0776d5b100fdb1b183d4f47a34e54fba70a8b099bd2998e759be4982f4cfcb`, 1318 entries.

## Checks
- **Integrity.** The manifests verify 3146/3146 and 3124/3124. `git am` reproduces all 4 hashes unsigned. `src/` equals the 15 paths. The package verifies 7/7 and the sources 377/377. Never more than 3 slots were held at once.
- **Build.** 565 modules give rc 0 and 0 errors in both forms. That covers the full downstream of `ClassP/DTIME` and `IterateFind`, through root `TCSlib` and both `Checks`, in 5534 s; the slowest module is `DetMod`, at 1510 s. The whole-tree check covers 1259 modules: OK.
- **Statements.** Headers and definition bodies are identical; only the three targets' docstrings change. decls2 gives 53 ADDED, 0 CHANGED, 0 REMOVED. E2 and E3 are byte-identical to their approved drafts.
- **Axioms.** All three targets, E1–E3, `inBPP_iff` and the helpers use only the standard three. 320 constants; no `sorryAx`.
- **Rule 10.** Only `IterateFind` fails (F-01); strict and coe agree. The coe controls are ALL_OK. The scan finds 0 foreign definitions.
- **Admissions.** 26 → 23.
- **Lint.** 92/101. Complexity goes from 25/391 to 25/390.
- **Content.**
  - **One machine gives both clauses, per H17.** The time bound comes through `decidesInTime_iff`/`computesFunInTime_iff`, and the envelope through `envelope_of_computesInTime`.
  - **The corollary** reads neither `DTIME` nor `DecidesInTime` by definition.
  - **The Gate 28 route** uses binary fuel `Nat.bits (2^w)`, a terminal rank in range, and `2^w+2 ≤ 3·2^w`.
  - **Theorem 180.1** has margins 7/12 and 5/12, with no finite table.

## Findings

| # | Severity | Finding | Disposition |
|---|---|---|---|
| F-01 | major | Rule 10. E1 `computesFunInTime_find` reads `hostTM`'s `k`/`State` fields by definition, giving 9 new seal failures. They are line-for-line copies of the 11 failures that the frozen `polyTimeComputable_find` already has at the base. The worker disclosed this (EX-02), and its proposed fix SR-02 went unanswered. | **Ruling (Seyoon, 2026-11-16): debt now, fix after.** Land as is. A maintainer follow-up PR will add SR-02-style typed-view readers (`ModuleHost`/`IterateFindHost`) and re-derive both E1 and `polyTimeComputable_find` through them, clearing all 20 failures. The re-derivation is already pre-approved. |
| F-02 | minor | SR-01 adds `Randomized.inBPP_iff` (`Iff.rfl`) to the frozen `Classes.lean`, which grows from 1403 to 1415 lines. Seyoon's approval had been recorded only in the delivery. | **Confirmed by Seyoon (2026-11-16)**, together with the inherited file-size exception. Accepted. |
| F-03 | info | The pre-approved re-derivation of `polyTimeComputable_find` was not taken up. E1 repeats 196 of the old proof's 228 lines (disclosed). | It is part of the F-01 follow-up. |
| F-04 | minor | The `inBPP_iff` docstring has no formula. | LE-doc, pending. |
| F-05 | info | The shared Mathlib cache lacks `Pow/NthRootLemmas.olean`, which `RootSchedule` imports. | Integration builds must fetch that root, using a narrowed cache get. |
| F-06 | info | Six unused-simp-argument warnings were copied from the old proof. There are near-relatives `randProb_bitsVal` and `abs_workTapePos_runFrom_sub_le`, but nothing is restated. | None. |
