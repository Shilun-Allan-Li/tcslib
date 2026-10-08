<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/EvenMoments.lean :: expect_sq_noiseOp_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The second moment of T_ρ f is nonnegative

**Claim.** For any `ρ : ℝ` and `f : BooleanFunc n`,
`0 ≤ expect (fun x => noiseOp ρ f x ^ 2)`. No hypothesis on `ρ` is required —
the integrand is a square and the uniform weight is positive.

**Proof.** `unfold expect uniformWeight` leaves `2⁻¹ ^ n * ∑ x, noiseOp ρ f x ^ 2`.
Split with `mul_nonneg (pow_nonneg (by positivity) _)`, then `Finset.sum_nonneg`
with `positivity` on each square. ∎

**Used in.** `BooleanAnalysis.Hypercontractivity.hypercontractivity_p_2_general` in `TCSlib/BooleanAnalysis/Hypercontractivity/Cube/EvenMoments.lean`; `BooleanAnalysis.Hypercontractivity.weak_two_function_hypercontractivity_one_bit` in `TCSlib/BooleanAnalysis/Hypercontractivity/Cube/General/Tensorization.lean`; `BooleanAnalysis.ThresholdFunctions.low_degree_moment_bound` in `TCSlib/BooleanAnalysis/ThresholdFunctions/LowDegreeNorm.lean`.
