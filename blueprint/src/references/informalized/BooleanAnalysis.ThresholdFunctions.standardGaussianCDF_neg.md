<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Profile.lean :: BooleanAnalysis.ThresholdFunctions.standardGaussianCDF_neg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian CDF Reflection Symmetry

**Claim.** For every real $x$, the standard Gaussian CDF satisfies $\Phi(-x)=1-\Phi(x)$.

**Proof.** The derivative of $t\mapsto\Phi(-t)+\Phi(t)$ is zero everywhere, by the reflection-sum derivative identity (`hasDerivAt_standardGaussianCDF_reflection_sum`). The function is therefore constant. To identify its value, let $t\to+\infty$: the first term tends to the CDF limit at $-\infty$, which is $0$, while the second tends to the CDF limit at $+\infty$, which is $1$. Thus the constant sum is $1$. Evaluating at $x$ and rearranging gives the stated symmetry.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.hasDerivAt_standardGaussianCDF_reflection_sum`.
