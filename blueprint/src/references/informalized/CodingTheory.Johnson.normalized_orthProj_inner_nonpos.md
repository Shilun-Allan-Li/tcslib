<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/JohnsonBound.lean :: normalized_orthProj_inner_nonpos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Normalizing the projections keeps their inner product non-positive

**Claim.** Under the hypotheses of `orthProj_inner_nonpos` (`‖u‖ = 1`,
`inner ℝ v w ≤ 0`, `inner ℝ v u ≤ 0`, `inner ℝ w u ≤ 0`), the normalized
projections also pair non-positively:
`inner ℝ (‖orthProj u v‖⁻¹ • orthProj u v) (‖orthProj u w‖⁻¹ • orthProj u w) ≤ 0`.

**Proof.**

1. `simp only [inner_smul_left, inner_smul_right]` pulls both scalars out,
   leaving `‖orthProj u v‖⁻¹ * (‖orthProj u w‖⁻¹ * ⟪orthProj u v, orthProj u w⟫)`.
2. The bracket is `≤ 0` by `orthProj_inner_nonpos u v w hu hvw hvu hwu`, and
   each `‖·‖⁻¹` is `≥ 0` by `inv_nonneg.2 (norm_nonneg _)`, so two nested
   applications of `mul_nonpos_of_nonneg_of_nonpos` finish.

**Remark.** The `orthProj u v ≠ 0` / `orthProj u w ≠ 0` arguments are unused
(hence named `_hv_ne`, `_hw_ne`) — non-negativity of `‖·‖⁻¹` suffices even when
the norm is `0`. They are kept so the signature matches the call site in
`rankin_bound_general`, which supplies them via `orthProj_ne_zero`.
