<!-- generated-by: proofmatch informalization (not_in_text) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Basic.lean :: innerProduct_self_nonneg -->
<!-- origin: boolean-ch02-social-choice-arrow run 352ab7ff3113 verdict not_in_text (0.82) -->

# Nonnegativity of the inner product on the diagonal

**Claim.** For every `f : BooleanFunc n`, `0 ≤ innerProduct f f`.

**Proof.** By definition `innerProduct f f = uniformWeight n * ∑ x, f x * f x`,
a product of a scalar and a sum, so `mul_nonneg` splits the goal in two.

1. Scalar factor: `uniformWeight n = (2 : ℝ)⁻¹ ^ n`, nonnegative by
   `pow_nonneg` applied to `0 ≤ (2 : ℝ)⁻¹` (`positivity`).
2. Sum factor: `Finset.sum_nonneg` reduces to one term at a time, and each
   `f x * f x` is a square, hence `mul_self_nonneg (f x)`. ∎

**Remark.** One of four deliberately granular bilinearity building blocks; this
is the positive-semidefiniteness half of the inner-product axioms, and is what
makes `l2Norm f = Real.sqrt (innerProduct f f)` well behaved.
