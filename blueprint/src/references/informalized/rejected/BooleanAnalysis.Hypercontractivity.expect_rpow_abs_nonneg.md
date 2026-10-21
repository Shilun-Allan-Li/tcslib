<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/EvenMoments.lean :: expect_rpow_abs_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Real-power L^p expectations are nonnegative

**Claim.** For any real exponent `p` and any `f : BooleanFunc n`,
`0 ≤ expect (fun x => |f x| ^ p)`. Note `^ p` is `Real.rpow`, so no sign
condition on `p` is needed. At a zero base the convention is `0^0 = 1`
and `0^p = 0` for `p ≠ 0`, including negative exponents.

**Proof.** `unfold expect uniformWeight`, leaving `2⁻¹ ^ n * ∑ x, |f x| ^ p`.
Then `mul_nonneg (pow_nonneg (by positivity) _)` for the weight, and
`Finset.sum_nonneg` plus `positivity` on each summand. ∎

**Used in.** `BooleanAnalysis.Hypercontractivity.lowDegree_concentration` in `TCSlib/BooleanAnalysis/Hypercontractivity/Applications/LowDegree.lean`; `BooleanAnalysis.Hypercontractivity.hypercontractivity_p_2_general` in `TCSlib/BooleanAnalysis/Hypercontractivity/Cube/EvenMoments.lean`; `BooleanAnalysis.Hypercontractivity.low_norms_hypercontractivity` in `TCSlib/BooleanAnalysis/Hypercontractivity/Cube/General/Bounds.lean`; `BooleanAnalysis.Hypercontractivity.noise_op_norm_dual` in `TCSlib/BooleanAnalysis/Hypercontractivity/Cube/General/Duality.lean`; `BooleanAnalysis.Hypercontractivity.one_function_iff_two_function_hypercontractivity`, `BooleanAnalysis.Hypercontractivity.weak_two_function_hypercontractivity_one_bit` in `TCSlib/BooleanAnalysis/Hypercontractivity/Cube/General/Tensorization.lean`; `BooleanAnalysis.Hypercontractivity.lpMean_const_mul`, `BooleanAnalysis.Hypercontractivity.lpMean_nonneg` in `TCSlib/BooleanAnalysis/Hypercontractivity/Cube/Reverse/Basic.lean`; `BooleanAnalysis.ThresholdFunctions.low_degree_l1_l2_sq`, `BooleanAnalysis.ThresholdFunctions.low_degree_moment_bound` in `TCSlib/BooleanAnalysis/ThresholdFunctions/LowDegreeNorm.lean`.
