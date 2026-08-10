<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/JohnsonBound.lean :: inner_shifted_expand -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Bilinear expansion of the shifted inner product

**Claim.** For `α : ℝ` and `x y : BitVec n`, writing
`shifted α x = pmOne x - α • ones`,

`⟪shifted α x, shifted α y⟫_[ℝ] = ⟪pmOne x, pmOne y⟫ - α * ⟪pmOne x, ones⟫ - α * ⟪pmOne y, ones⟫ + α^2 * ⟪ones, ones⟫`

(all inner products over ℝ). This is bilinearity of `⟪·,·⟫` applied to the
two-term shift, with no hypotheses on `α`, `x`, `y`.

**Proof.**

1. `unfold shifted` replaces both arguments by `pmOne _ - α • ones`.
2. `simp [RCLike.wInner]` turns every inner product on both sides into a
   coordinate sum over `Fin n`.
3. `simp [mul_sub, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum, pow_two]`
   distributes the products over the subtractions and pulls the scalar `α`
   out of the sums, so both sides are ℝ-linear combinations of the same four
   sums.
4. `simp [mul_comm, mul_assoc, sub_eq_add_neg]` normalizes the factor order
   and `ring` closes the resulting identity.

**Remark.** A purely formal step: it is separated out only so that
`inner_shifted_le_expr` can rewrite the three resulting inner products by
their closed forms independently.
