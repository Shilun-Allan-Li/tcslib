<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/Entropy.lean :: am_gm_sqrt_le_half_sum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Two-term AM–GM

**Claim.** For reals `0 ≤ a` and `0 ≤ b`, `Real.sqrt (a * b) ≤ (a + b) / 2`: the
geometric mean of two nonnegative reals is at most their arithmetic mean. A
`private` helper.

**Proof.** Three lines.

1. `hab_sq`: `a * b ≤ ((a + b) / 2) ^ 2`, which is `nlinarith [sq_nonneg (a - b)]`
   — i.e. `(a-b)² ≥ 0`.
2. Monotonicity of the square root (`Real.sqrt_le_sqrt`) turns this into
   `√(a·b) ≤ √(((a+b)/2)²)`.
3. `Real.sqrt_sq` removes the square, the side condition `0 ≤ (a+b)/2` coming from
   `linarith` on `ha`, `hb`. ∎

**Used in.** `stirling_comb_bound`, to bound `√(a·b) ≤ n/2` when `a + b = n`; this
is what converts the product of the two Stirling factors into a single factor
linear in `n`.
