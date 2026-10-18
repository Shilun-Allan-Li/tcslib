# External audit pack — C1-UN: the universal NDTM's three corollaries proved (PR #129, a fill gate)

Campaign: the Arora-Barak chapters 3-4 plan, C1 (the nondeterministic time hierarchy, [AB09, Theorem
3.2]). The fill brief C1-UN (`campaign/fills/c1/briefs/c1-fill-universal.md`) has four targets in
`TCSlib/Complexity/Diagonalization/NTimeHierarchy.lean`:
- the universal NDTM `Turing.exists_timed_universal_NDTM`;
- the exponential decider `Turing.exists_ndAcceptsWithin_decider` (BF);
- the positive-bound hierarchy `Complexity.ntime_hierarchy_of_pos` (H′);
- the showcase `Complexity.NTIME_linear_ssubset_square` (S).

The worker's delivery (`campaign/fills/c1/reports/universal-1-REPORT.md`) proves **BF, H′ and S**.
The universal stays `sorry`: its setup's scratch cleanup needs a published contract for the pair
extractor's halting configuration (the worker's escalation, confirmed by the review; an API PR,
#132, adds it). The maintainer's review is `campaign/fills/c1/reviews/universal-1/REVIEW.md`. **It
lands as a partial**, as earlier partials did.

**The head:** `lean/c1-un-partial` at `3a1678d1`, two commits on the campaign branch:
- `8449bdd3`: the worker's commit `483fb579`, cherry-picked from its verified bundle;
- `3a1678d1`: the maintainer's. The worker's four "fill appendix" paragraphs are removed or
  reduced to the formal route's facts, in public-facing terms (no campaign labels), and the
  module's status text is corrected. Docstrings only.

## Brief for the auditor

1. **Freeze.** Against the base: no statement changed; the only body changes are the three proofs
   (`evidence/freeze.txt`); no declaration added or removed.
2. **The proofs.**
   - **BF:** `Turing.ndAcceptsWithin_decider_of_universal` applied to the universal.
   - **H′:** `NTIME.mono` both ways, with the factor `2` absorbed into the membership constant.
   - **S:** `Complexity.timeConstructible_poly` at `(1, 0)` and `(1, 1)`, and domination at
     `N = 3A + 4`.

   Are they correct and on the brief's route? Do they read other files' definitions only through
   published lemmas? The review's seal test covered the 8 definitions they reach.
3. **What remains admitted.** The three proved results reach `sorryAx` only through the universal,
   `ntime_hierarchy` and the exhaustive decider (`evidence/elab-NTimeHierarchy.out`). Is that
   exactly the brief's dependency structure?
4. **The docstrings** (the maintainer's commit): are they accurate, and free of development
   narrative?
5. **The escalation:** is the reported gap (the extractor's terminal configuration) real at the
   base, and does #132's `FinTM.pairExtractTM_fst_run` close it?

## Repository-side attestations (verify or challenge)

- **Elaboration** against `oleans-lx2b` (the campaign tip's snapshot): 0 errors; 2 `sorry` warnings,
  the universal and `ntime_hierarchy` (the module had 5).
- **The review:** integrity of the bundle; a seal test; the 72-check import probe; the v3 screen
  67 → 70 declarations, with no new pair.
- **Lint:** `Diagonalization/` 0 FAIL, 1 WARN, unchanged.
- **Replay:** `replay-lun.sh`, 2 modules (`NTimeHierarchy` and the `Diagonalization` facade), from
  `oleans-lx2b`. **Passed (user, 2026-10-18):** 2 of 2 at `3a1678d1`, 0 failed, static-equal (2).

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `campaign/standards/TEMPLATE.md`. Findings go verbatim into
`campaign/gates/47-c1-universal-fill/findings.md`. The gate closes when it has zero blockers and zero
majors.

**Deliver your findings as a downloadable Markdown file named `c1-universal-fill-findings.md`** (the
findings table and the verdict line, no other wrapping), and also paste its content in your reply.
