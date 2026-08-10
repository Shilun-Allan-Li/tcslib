<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/JohnsonBound.lean :: alpha_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The shift parameter is nonnegative

**Claim.** For all `n d : ℕ`, `0 ≤ alpha n d`, where
`alpha n d = Real.sqrt ((n - 2 * d) / n)`.

**Proof.** Immediate from `Real.sqrt_nonneg _`: a real square root is
nonnegative regardless of the sign of its argument, so no hypothesis relating
`d` to `n` is needed.

**Used in.** `binary_johnson_card_bound`, which must supply `0 ≤ α` to
`binary_johnson_card_bound_parametric` and to `inner_shifted_le_expr`.
