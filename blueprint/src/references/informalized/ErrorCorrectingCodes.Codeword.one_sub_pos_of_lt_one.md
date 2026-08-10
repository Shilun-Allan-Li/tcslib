<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/Basic.lean :: one_sub_pos_of_lt_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# 1 − p is positive below one

**Claim.** For a real `p` with `p < 1`, we have `0 < 1 - p`. There is no lower
bound on `p`; the statement is about an arbitrary real strictly below one.

**Proof.** Immediate from `exact sub_pos.mpr hp` — the reverse direction of
Mathlib's `sub_pos : 0 < a - b ↔ b < a`.

Granular helper, but the most-used of this group. Its role is to supply the
positivity side condition on `1 - p` demanded by the third summand
`(1-p) * Real.logb q (1 - p)` of `qaryEntropy`, and by the derivative and
monotonicity arguments built on it.

**Used in.** `Entropy.lean` at five call sites (`h_one_sub_p`, `hp₂`, `h1p`
twice, `h1p_0`), and inside `Basic.lean` itself as the final step of both
`mul_one_sub_pos` and `one_sub_pos_of_le_one_sub_inv`.
