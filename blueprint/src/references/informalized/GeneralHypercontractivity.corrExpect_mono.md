<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/General.lean :: corrExpect_mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Monotonicity of the kernel-weighted expectation

**Claim.** Let `0 ≤ ρ ≤ 1` and let `h h' : BoolCube n → BoolCube n → ℝ` satisfy
`h x y ≤ h' x y` for all `x, y`. Then

`uniformWeight n * ∑ x, ∑ y, noiseKernel ρ x y * h x y
   ≤ uniformWeight n * ∑ x, ∑ y, noiseKernel ρ x y * h' x y`.

**Proof.** Monotonicity is inherited factor by factor.

1. `apply_rules [mul_le_mul_of_nonneg_left, Finset.sum_le_sum]` reduces to the
   pointwise comparison plus nonnegativity of the outer constant.
2. Pointwise: two nested `Finset.sum_le_sum`, then
   `mul_le_mul_of_nonneg_left (hle x y) (noiseKernel_nonneg hρ0 hρ1 x y)` — the
   only place the hypotheses `0 ≤ ρ ≤ 1` are used.
3. Outer constant: `uniformWeight n = (2⁻¹)^n ≥ 0` by `pow_nonneg`.

**Note.** A deliberately granular helper. As written it has no consumers
anywhere in the repository (see report).
