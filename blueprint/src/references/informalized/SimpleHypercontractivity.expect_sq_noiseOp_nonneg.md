<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Simple.lean :: expect_sq_noiseOp_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The second moment of T_ρ f is nonnegative

**Claim.** For any `ρ : ℝ` and `f : BooleanFunc n`,
`0 ≤ expect (fun x => noiseOp ρ f x ^ 2)`. No hypothesis on `ρ` is required —
the integrand is a square and the uniform weight is positive.

**Proof.** `unfold expect uniformWeight` leaves `2⁻¹ ^ n * ∑ x, noiseOp ρ f x ^ 2`.
Split with `mul_nonneg (pow_nonneg (by positivity) _)`, then `Finset.sum_nonneg`
with `positivity` on each square. ∎

**Used in.** `hypercontractivity_p_2_general` (as `hE₂_nn`, which drives both the
`E₂ = 0` branch and the strict-positivity step `lt_of_le_of_ne`), and in
`Hypercontractivity/General.lean`. Granular by design: the same three-line
argument as `expect_rpow_abs_nonneg`, isolated so the duality proof can cite it.
