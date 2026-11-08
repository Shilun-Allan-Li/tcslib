<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/LinearThresholdInfluence.lean :: BooleanAnalysis.ThresholdFunctions.fourierCoeff_singleton_eq_expect_derivative -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Singleton Fourier Coefficient and Derivative

**Claim.** The Fourier coefficient of a function at the singleton $\{i\}$ equals the expectation of its derivative in coordinate $i$.

**Proof.** First identify the derivative at each point with the coordinate-averaging operator applied to the function $x\mapsto f(x)\sigma(x_i)$. Indeed, fixing coordinate $i$ to the two possible bits makes this average equal to the difference of the two corresponding function values divided by two. Averaging this identity over the cube, the coordinate-averaging operator preserves expectation (`expect_expectationOperator`). The resulting expectation is that of $f(x)\sigma(x_i)$, which by the singleton-character formula is precisely the Fourier coefficient at $\{i\}$.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.expect_expectationOperator`.
