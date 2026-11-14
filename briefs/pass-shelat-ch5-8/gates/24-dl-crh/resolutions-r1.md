# Gate 24 · resolutions, round 1 · IN PROGRESS

Codex's verdict is **HOLD**: 0 blockers, 1 major, 2 minors and 0 notes.
- **Findings:** `findings/gate24-dl-crh-findings.md`, SHA-256 `f29e4cb936dff2a470c58ccd405f6f37d755297eeefdc462e8bfd99494a4b689`.
- **Audited head:** `649c4888f23fbb9df71d555e952d1149a0aaa00b`.

| # | Severity | Disposition |
|---|---|---|
| G24-01 | major | **Being fixed by maintainer landing edit LE-reuse**, proof only. `inputWord_take` is re-proved from the public `take_ofFn_castLE` (`Asymptotic/ReductionSupport.lean`). Where it is just as easy, `inputWord_split` is also re-proved from `ofFn_eq_init_append`, which clears that DL-41 item. Both statements stay unchanged. |
| G24-02 | minor | **Erratum** in `fills/dl-crh/final-r1/review.md`, Content step 2. A collision with *equal* selectors is impossible; the review had said *different*. The Lean proof and the target's sketch were already correct. |
| G24-03 | minor | **Erratum** to the pack, ruling 3. FAIL lines are identical at the head and the tip, but two `DiscreteLog` WARN lines change (`1192 → 1212` lines; missing readers `6 → 5`, after `expSampleRaw_eq`). The counts stay at 92 FAIL / 102 WARN. These two WARN changes are the accepted ones. The pack is pinned, so the correction is recorded here. |
