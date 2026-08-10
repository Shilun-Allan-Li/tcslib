<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/Entropy.lean :: qary_entropy_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Positivity of the q-ary entropy

**Claim.** Let `q = Fintype.card α` for a finite field `α`, and let `0 < p ≤ 1 - 1/q`.
Then the `q`-ary entropy expression is strictly positive:
`0 < p · logb q (q-1) - p · logb q p - (1-p) · logb q (1-p)`. (The statement is
written out in `Real.logb` rather than as `qaryEntropy q p`, but it is the same
expression.)

**Proof.** Reduce to natural logarithms, then to positivity of the two entropy terms.

1. `2 ≤ q`: `α` is a nontrivial fintype, so `Fintype.one_lt_card` gives `1 < q`
   (`Nat.succ_le_iff`). Hence `1 < (q:ℝ)`, `0 < (q:ℝ)`
   (`natCast_one_lt_of_two_le`, `natCast_pos_of_two_le`) and `0 < Real.log q`
   (`Real.log_pos`).
2. `p < 1` from `p ≤ 1 - 1/q` (`lt_one_of_le_one_sub_inv`), so `0 < 1 - p < 1`
   (`one_sub_pos_of_lt_one`).
3. `suffices` it is enough to prove the same inequality with `Real.log` in place of
   `Real.logb`: since `Real.logb b x = Real.log x * (Real.log b)⁻¹` and
   `0 < Real.log q`, dividing preserves positivity (`div_pos_iff`), and
   `distrib_three_right` distributes the `(Real.log q)⁻¹` factor across the three
   summands so the result matches the goal syntactically.
4. `h_ent_pos`: `0 < -p·log p - (1-p)·log (1-p)`. Both `log p < 0` and
   `log (1-p) < 0` by `Real.log_neg` (arguments strictly between `0` and `1`), so
   each product is positive by `mul_neg_of_pos_of_neg`; `linarith` adds them.
5. `0 ≤ log (q-1)`: `1 ≤ (q:ℝ) - 1` because `2 ≤ (q:ℝ)`, so `Real.log_nonneg`
   applies, and `mul_nonneg` makes `p · log (q-1)` nonnegative.
6. `add_pos_of_nonneg_of_pos` combines steps 4 and 5; `ring_nf` matches the
   associativity of the goal. ∎

**Used in.** `list_decoding_capacity` (ListDecoding.lean), where `0 < qaryEntropy q ρ`
is needed to give the constructed code a positive rate.
