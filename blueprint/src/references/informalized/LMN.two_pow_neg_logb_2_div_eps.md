<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN.lean :: two_pow_neg_logb_2_div_eps -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# `2^(−log₂(2/ε)) = ε/2`

**Claim.** For `ε : ℝ` with `0 < ε`,

`(2 : ℝ)⁻¹ ^ Real.logb 2 (2 / ε) = ε / 2`

(the exponentiation is `Real.rpow`, the exponent being a real logarithm).

Exponentiating base `2` undoes `logb 2`, so `2^(log₂(2/ε)) = 2/ε` and the
reciprocal is `ε/2`. This is the identity that turns the abstract degree cutoff
`l = log₂(2/ε)` into the concrete error budget `ε/2`.

**Proof.** Three rewrites.

1. `Real.inv_rpow` (with `0 ≤ 2` by `norm_num`) moves the inverse outside:
   `2⁻¹ ^ a = (2 ^ a)⁻¹`.
2. `Real.rpow_logb` (base `≠ 0, 1` by `norm_num`, argument positive by
   `positivity`) collapses `2 ^ logb 2 (2/ε)` to `2 / ε`.
3. `field_simp` finishes `(2 / ε)⁻¹ = ε / 2`.

**Used in.** `LMN/LMNConcentration.lean`, as the final step of a `calc` chain
bounding the tail Fourier weight by `ε/2`.
