<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/OneBit.lean :: cauchy_schwarz_bool -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Cauchy-Schwarz for the Boolean inner product

**Claim.** For `f g : BooleanFunc n`,
`innerProduct f g ≤ (expect (fun x => f x ^ 2)) ^ (1/2) * (expect (fun x => g x ^ 2)) ^ (1/2)`
— i.e. `⟨f, g⟩ ≤ ‖f‖₂ ‖g‖₂` for the uniform-measure inner product. Stated with
real `rpow` exponent `1/2`, one-sided (no absolute value on the left).

**Proof.** Reduce to the unweighted Cauchy-Schwarz on the sum.

1. `norm_num [← Real.sqrt_eq_rpow]` turns both `(·) ^ (1/2)` into `Real.sqrt`, then
   unfold `innerProduct` and `expect`.
2. `← Real.sqrt_mul` merges the two roots (side goal: the first expectation is
   non-negative, from `pow_nonneg` on the weight and `Finset.sum_nonneg` of squares).
3. `Real.le_sqrt_of_sq_le` reduces to comparing squares.
4. `Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f g` gives
   `(∑ x, f x * g x) ^ 2 ≤ (∑ x, f x ^ 2) * (∑ x, g x ^ 2)`; multiplying by the
   non-negative `uniformWeight n ^ 2` (`mul_le_mul_of_nonneg_left`, `sq_nonneg`) and
   `ring` matches the goal. ∎

**Used in.** `noise_operator_duality` (deriving `(2, p')`-hypercontractivity from the
`(p, 2)` case) and `weak_two_function_hypercontractivity_one_bit` in
`Hypercontractivity/General.lean`, where the two noise operators are split apart.
