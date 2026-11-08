<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Randomization/General.lean :: BooleanAnalysis.Hypercontractivity.half_noise_norm_le_randomization -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Half-Noise Norm Bound by Randomization

**Claim.** For a finite product probability space, a real-valued function, and $q\geq1$, the $q$-moment norm of the half-noise of the function is at most its randomization moment norm.

**Proof.** For each product point $x$, the half-noise is the uniform average over Boolean masks of the conditional expectations of the corresponding randomizations (`randomization_condExp_average`). The mask weights are nonnegative and sum to one; the latter normalization follows from `expect_const`. Convexity of $z\mapsto |z|^q$ for $q\geq1$, in the weighted form `weighted_abs_rpow_sum_le`, therefore bounds the $q$th absolute power of this average by the weighted average of the conditional $q$th absolute powers. Multiply by the nonnegative product mass at $x$ and sum over $x$ to obtain the first moment inequality.

Exchange the two finite sums to put the mask expectation outside the product expectation. For each mask, conditional expectation does not increase the $q$th absolute moment, by `condExp_moment_le`. Averaging this inequality over masks preserves it (`expect_mono`). Exchange the finite sums back to identify the result as the moment inside the randomization norm. Finally, taking the power $1/q\geq0$ preserves the inequality because the moments are nonnegative. This gives the asserted norm bound.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.expect_const`, `BooleanAnalysis.Hypercontractivity.randomization_condExp_average`, `BooleanAnalysis.Hypercontractivity.RandomizationAux.weighted_abs_rpow_sum_le`, `BooleanAnalysis.expect_eq_fintypeExpect`, `BooleanAnalysis.Hypercontractivity.RandomizationAux.condExp_moment_le`, `BooleanAnalysis.ThresholdFunctions.expect_mono`.
