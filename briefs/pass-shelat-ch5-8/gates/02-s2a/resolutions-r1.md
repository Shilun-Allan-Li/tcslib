# Gate 02 (S2a, #185): round 1 resolutions

- **Round 1:** findings `gate02-s2a-findings.md`, verbatim, SHA-256
  `fed1bc4afbc4d829aa71c4dcc455ef514709836dfd7f686a45fbdd4138113709`; head
  `597eef43ccd3c8bfafe0c0c16a2444b12adc1644`. Counts: **1 blocker, 3 majors, 6 minors, 2 notes.**
  The gate does not close.
- **Review:** `review/subagent-review.md` found 11 true and 1 partly true (#1), none false, and no
  severity change. Its exact-rational model of the counterexamples is
  `review/scripts/model.py.txt`.
- **Rulings (user, 2026-11-05):** #1 D8's execution semantics, with early returns; #4 strict or
  truncated simulators (a declared deviation); #10 reuse of the concrete layer's hybrid lemmas.
- **Repairs:** two commits on #185's branch, after `597eef43`:
  - `14e5988633b949811f774a15583d4967397bf292`, the round 1 repairs;
  - `586510c1416afa21881b9a42b5a8d0578c9bd749`, completing #8. The maintainer's check of each
    "Fixed" row against the code found the [Sho04] and [BR06] numbers still in `Hopping.lean`'s
    reference block.

  Round 2 audits the head `586510c1416afa21881b9a42b5a8d0578c9bd749`.
- **Verified at `586510c1`** (`evidence-r2/`):
  - a clean replay of the 9-module closure: 9/9 pass, 0 errors, 0 warnings;
  - `#print axioms` for all 75 theorems: only `propext`, `Classical.choice` and `Quot.sound`;
  - both style lints: 0 findings; no line over 100 characters;
  - the name screen: no new clash.

  The full repair diff is `evidence-r2/repair.diff.txt`.

| # | Severity | Resolution |
|---|---|---|
| 1 | blocker | **Fixed (API change).** `ExecOutcome` (`done` / `outOfFuel` / `sentAfterEnd`). `Party.close` replaces `finish`: the waiting party's pending send is answered `none`, it may draw coins, and a send is reported. `endWith`; `exec`, where a return costs no fuel. A deviation note (D8; early returns allowed). Three `rfl` sanity examples (fuel counts messages; a send after the end is reported). `finish` is removed. To be confirmed with Frederick under F-2. |
| 2 | major | **Fixed.** The views docstring is corrected. New `Party.Obs`, `stepT`, `closeT`, `endWithT` and `execT`, the traced execution recording each party's received messages (the second mover's first message first) and coins. `execT_outcome` proves it has `exec`'s outcome. |
| 3 | major | **Fixed (generalization).** `prob_eq_until_bad`/`identical_until_bad` take the semantic hypothesis (from a good state, the same law to good successors). `hagree_of_eq` recovers the syntactic form; `identical_until_bad_init` handles a sampled initial state (the review's missed item 3). A deviation note against [BR06]. |
| 4 | major | **Recorded (ruled).** Strict or truncated simulators for Thm 175.1, carrying D8 into ch. 7: `PerfectZKAbort` composes to statistical ZK with error `Q·2^-k`. Recorded in the plan's decision log and the S2 design note; the inventory row already carried the debt (pack erratum E1). No framework change. |
| 5 | minor | **Fixed** with #1: fuel is the message budget. |
| 6 | minor | **Fixed:** "a well-founded tree …; finite with finite answer types". |
| 7 | minor | **Fixed:** VCVio tags on `ProbComp`, `sampleFin`, `QueryImpl.comp` and `simulate_comp`; the reference block lists `ProbComp/Basic` and `QueryImpl/Compose`; `CITATION-VCVio.md` names the authors per module. |
| 8 | minor | **Fixed:** [PS10, Lemma 71.6]. [Sho04] and [BR06] section and lemma numbers are dropped (unverifiable from this session; completed in `586510c1`). |
| 9 | minor | **Fixed:** the `accept_nonneg` and `expect_mono_of_allOutputs` docstrings. |
| 10 | minor | **Fixed (ruled reuse):** `advantage_hybrid` is the concrete layer's `abs_sub_le_sum_hybrids`, and the new `exists_advantage_hybrid_gap` is its `exists_hybrid_gap` ([PS10, Lemma 71.6]). It imports `Foundations/Probability.lean`, which uses only Mathlib (pack erratum E2). |
| 11 | note | **Recorded:** exact non-dyadic sampling is not fair-bit-efficient. The machine bridge (S2b) restricts to dyadic sampling, or uses the concrete layer's truncated rejection sampler. |
| 12 | note | **Recorded:** the bridges and efficiency are S2b, scheduled. |
| M1 (review) | minor | **Fixed:** the collision bound's docstring is scoped to one fresh draw. The adaptive repeated-nonce lemma is scheduled with the statement phase. |
| M2 (review) | minor | **Fixed:** source tags on `prob_mem_le` and the guess-the-bit declarations. |
| M4 (review) | note | **Fixed:** the S2 design note is synchronized with the code. |
