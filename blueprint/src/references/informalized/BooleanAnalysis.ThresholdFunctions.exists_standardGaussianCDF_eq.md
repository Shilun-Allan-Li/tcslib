<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/GaussianTail.lean :: BooleanAnalysis.ThresholdFunctions.exists_standardGaussianCDF_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Attainment of interior Gaussian probabilities

**Claim.** For every $\alpha$ strictly between $0$ and $1$, the standard Gaussian cumulative distribution function takes the value $\alpha$ at some real number.

**Proof.** The Gaussian cumulative distribution function tends to $0$ as its argument tends to negative infinity and to $1$ as its argument tends to positive infinity. Since $0<\alpha<1$, choose real numbers $a$ and $b$ far enough toward these respective ends that the value at $a$ is below $\alpha$ and the value at $b$ is above $\alpha$. Strict monotonicity of the CDF (`standardGaussianCDF_strictMono`) ensures $a\le b$. The function is continuous (`continuous_standardGaussianCDF`), so the intermediate value theorem on $[a,b]$ gives a point $t$ with value exactly $\alpha$.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.standardGaussianCDF_strictMono`, `BooleanAnalysis.ThresholdFunctions.continuous_standardGaussianCDF`.
