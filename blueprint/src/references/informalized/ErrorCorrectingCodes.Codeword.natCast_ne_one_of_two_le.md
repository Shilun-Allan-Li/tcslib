<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/Basic.lean :: natCast_ne_one_of_two_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# An alphabet size at least two is not one

**Claim.** For `q : ℕ` with `2 ≤ q`, the cast satisfies `(q : ℝ) ≠ 1`.

**Proof.** One line:
`linarith [show (1 : ℝ) < q from natCast_one_lt_of_two_le hq]`.

- `natCast_one_lt_of_two_le hq` gives the strict inequality `1 < (q : ℝ)`.
- `linarith` closes the disequality goal; it handles `≠` here by refuting the
  equation against that strict bound.

Granular helper packaging the inequality in the *shape* Mathlib's logarithm API
asks for: lemmas such as `Real.logb` base-rewriting and `Real.rpow_logb` take a
side condition `b ≠ 1` rather than `1 < b`, so a bare application of
`natCast_one_lt_of_two_le` would not unify.

**Used in.** `Entropy.lean`, at the `hq₃` and `hq_ne1` steps.
