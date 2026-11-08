<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/GaussianDensity.lean :: BooleanAnalysis.GaussianSpace.integral_indicator_gaussian_affine -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Affine Gaussian Indicator Density Formula

**Claim.** For a measurable set $A\subseteq\mathbb R$ and real $c,s$ with $s\ne0$, the integral of its indicator at $c+sy$ against the standard Gaussian measure equals the integral of the indicator against the Gaussian density with mean $c$ and variance $s^2$.

**Proof.** Set $v=s^2$, viewed as a nonnegative variance parameter. Since $s\ne0$, we have $v\ne0$. The image of the standard Gaussian measure under the affine map $y\mapsto c+sy$ is the Gaussian measure with mean $c$ and variance parameter $v$: factor the map into scaling by $s$ and translation by $c$, and use the corresponding transformation laws for Gaussian measures. The change-of-variables formula for integration against a mapped measure therefore identifies the original integral with the integral of the indicator under that Gaussian measure. Finally, the Gaussian density formula expresses that integral as the Lebesgue integral of the indicator multiplied by the density with mean $c$ and variance $s^2$.
