<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/GaussianTail.lean :: BooleanAnalysis.ThresholdFunctions.gLog_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positivity of the Gaussian tail scale

**Claim.** The quantity $L(t)=2\log(1/\Phi(t))$ is positive for every real $t$.

**Proof.** The standard Gaussian CDF is positive and strictly less than $1$ (`standardGaussianCDF_pos` and `standardGaussianCDF_lt_one`). Consequently its reciprocal is strictly greater than $1$. The logarithm is positive on numbers greater than $1$, so $\log(1/\Phi(t))>0$, and multiplying by $2$ preserves positivity.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.standardGaussianCDF_pos`, `BooleanAnalysis.ThresholdFunctions.standardGaussianCDF_lt_one`.
