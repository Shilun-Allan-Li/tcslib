<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Products/Applications.lean :: BooleanAnalysis.Hypercontractivity.product_laplacian_abs_moment_le_influence -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Laplacian Moment Bound

**Claim.** For a Boolean-valued function on a finite product probability space and any coordinate i, the expected pth absolute moment of its coordinate Laplacian is at most the influence of that coordinate whenever 1 ≤ p ≤ 2.

**Proof.** For each real z, apply the convexity estimate (1+s)^α ≤ 1+αs for s ≥ −1 and 0 ≤ α ≤ 1 with s=|z|−1 and α=p−1. Multiplying by |z|≥0 and simplifying gives |z|^p ≤ (2−p)|z|+(p−1)z². Apply this pointwise with z the coordinate Laplacian and take expectations; nonnegative product masses preserve the inequality. The Boolean residual identity says that the expected absolute value of the residual equals its expected square, hence equals the coordinate influence. By definition, the expected square is also that influence. The resulting upper bound is (2−p)Iᵢ+(p−1)Iᵢ=Iᵢ.

**Key facts.** `BooleanAnalysis.Hypercontractivity.product_boolean_residual_abs_expect`.
