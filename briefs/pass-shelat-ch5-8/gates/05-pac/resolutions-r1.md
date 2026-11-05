# Gate 05 (PAC layer, #194): round 1 resolutions

- **Round 1:** findings `findings/gate05-pac-findings.md`, verbatim, SHA-256
  `06adae4b5571db4b84c221eeb838f50e9ba5b21dbc89e340529907ed54ca2f16`; head
  `44d27f39c233849a3a30a117bf15434610e485e9`. Counts: **0 blockers, 1 major (F1), 8 minors, 7 notes.**
- **Review:** `review/gate05-review.md`: 11 true, 5 partly true, none false; F5 moved from minor to
  note.
- **Rulings (user, 2026-11-05):** G5-1, remove `PACLearnable` and `pacLearnable_iff` and rewrite the
  deviation as a statement about single learners; G5-2, move `FinDist.probTrue` into `FinDist.lean`
  later, in a small PR to `main`.
- **Repair:** one commit on #194's branch, `6b781240bc438a103291c74b2ffefaa910f1a70d` (full diff
  `evidence-r2/repair.diff.txt`). Elaboration of the four changed modules and lint: maintainer's
  re-check (`evidence-r2/checks.log`). Axioms (worker's run): 37 of the 38 theorems print within
  `propext`, `Classical.choice` and `Quot.sound`; `PAC.label_apply` uses none; no `sorryAx`.

| Finding | Severity | Resolution |
|---|---|---|
| F1 | major | **Fixed** (G5-1). `PACLearnable` and `pacLearnable_iff` removed. The "Fixed parameters" deviation is replaced by a single-learner statement ([KV94, §1.2.1]). `PACLearns`'s docstring ("a PAC learner at fixed parameters"), the `PAC.lean` contents line and `Prediction.lean:27–28` rewritten. Nothing says that the negation of a fixed-parameter predicate is non-learnability, and [SSBD14, Def 3.1] is no longer said to require a polynomial sample size. |
| F2 | minor | **Fixed.** Parameter ranges and degenerate cases stated for `PACLearnsUnder`, `PACLearns`, `WeakLearnsUnder` and `WeakLearns`. `not_pacLearnsUnder_of_neg` reworded ("a witness outside the sources' range"). **New:** an in-range witness `not_pacLearnsUnder_const_pair` (no examples, the two constant concepts on a one-point domain, `ε < 1`, `δ < ½`). An "Unrestricted parameters" deviation bullet is added. The review's text "`ε < 0` or `δ < 0`" was corrected to "either `δ < 0`, or `ε < 0` and `δ < 1`". |
| F3 | minor | **Fixed.** An "Improper hypotheses" deviation bullet. |
| F4 | minor | **Fixed.** A "Coins" deviation bullet; the coins are not generalized to `FinDist ρ` (the review's advice). |
| F5 | note (was minor) | **Fixed** (documentation): `not_weakLearnsUnder_of_predictAdv_le` says the confidence must be below the gap. |
| F6 | minor | **Fixed.** `PACLearnsUnder` tagged as the fixed-distribution variant of [KV94, §1.2.1] / [SSBD14, Def 3.1]; `WeakLearns(Under)` cite [KV94, §4.1] and state the fixed real edge and confidence. |
| F7 | minor | **Fixed.** The [PS10] reading is on `predictSuccess`; `predictAdv` has its tag and the two-sided reading. |
| F8 | minor | **Fixed.** The four `_iff` lemmas, `accuracyProb_eq`, `predictSuccess_eq` and `expectedErr_eq` state their formulas in their docstrings. |
| F9 | minor | **Recorded** (G5-2): `probTrue` moves into `FinDist.lean` in a follow-up PR to `main` (queued). |
| F10 | note | No change (observation). |
| F11 | note | **Fixed.** `Samples.lean` says "values at most `1`". |
| F12 | note | **Fixed.** `ε ≥ 0` and `γ' ≤ ½` stated in `Prediction.lean`'s module docstring; the optional sharper lemmas are not added. |
| F13 | note | No change (the marginal lemma for `iid` is not needed by any statement). |
| F14 | note | **Partly fixed.** The unused [Vad12] reference is dropped; the [SSBD14, §2.3.1] location stays until checked against the book. |
| F15 | note | Recorded: the pack's attestations are refreshed in this round (`evidence-r2/`). |
| F16 | note | **Resolved** by the review from the source text (p. 179). |
