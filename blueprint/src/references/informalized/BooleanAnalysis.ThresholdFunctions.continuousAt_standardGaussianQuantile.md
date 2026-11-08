<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Profile.lean :: BooleanAnalysis.ThresholdFunctions.continuousAt_standardGaussianQuantile -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Continuity of the Gaussian quantile

**Claim.** For every $a\in(0,1)$, the standard Gaussian quantile $Q$ is continuous at $a$.

**Proof.** The quantile is strictly increasing on $(0,1)$, and its image there is all of $\mathbb R$. Indeed, given any $x\in\mathbb R$, the Gaussian CDF value $\Phi(x)$ lies strictly between $0$ and $1$, by positivity and the strict upper bound for the CDF (standardGaussianCDF_pos and standardGaussianCDF_lt_one). The identity $Q(\Phi(x))=x$ (standardGaussianQuantile_eq) therefore shows that every real number is in the image. A strictly monotone function is continuous at any point whose domain contains a neighborhood of that point and whose image contains a neighborhood of its value. Here $(0,1)$ is a neighborhood of $a$, and the image is all of $\mathbb R$, so this criterion gives continuity at $a$.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.standardGaussianQuantile_strictMonoOn`, `BooleanAnalysis.ThresholdFunctions.standardGaussianCDF_pos`, `BooleanAnalysis.ThresholdFunctions.standardGaussianCDF_lt_one`, `BooleanAnalysis.ThresholdFunctions.standardGaussianQuantile_eq`.
