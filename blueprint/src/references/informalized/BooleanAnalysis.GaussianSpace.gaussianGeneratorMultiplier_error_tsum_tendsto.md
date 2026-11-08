<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Hermite/Generator.lean :: BooleanAnalysis.GaussianSpace.gaussianGeneratorMultiplier_error_tsum_tendsto -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Convergence of the Summed Multiplier Error

**Claim.** If $\sum_i(d_ic_i)^2$ is finite, then as $t\to0$ through positive values the sum of squared multiplier errors tends to zero.

**Proof.** For each fixed $i$, the multiplier tends to $d_i$ as $t$ approaches zero from above (`gaussianGeneratorMultiplier_tendsto`). Subtracting $d_i$, multiplying by $c_i$, and squaring therefore shows that the corresponding error term tends to zero. For every positive $t$, the squared error is bounded by $(d_ic_i)^2$ (`gaussianGeneratorMultiplier_error_sq_le`), and these bounds are summable by hypothesis. The dominated convergence theorem for series now allows the limit to pass through the sum; the resulting sum is the sum of zeros, hence zero.

**Key facts.** `BooleanAnalysis.GaussianSpace.gaussianGeneratorMultiplier_tendsto`, `BooleanAnalysis.GaussianSpace.gaussianGeneratorMultiplier_error_sq_le`.
