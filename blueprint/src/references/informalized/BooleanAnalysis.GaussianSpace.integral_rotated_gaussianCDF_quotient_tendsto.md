<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Halfspace.lean :: BooleanAnalysis.GaussianSpace.integral_rotated_gaussianCDF_quotient_tendsto -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Integrated Gaussian Crossing Limit

**Claim.** For each real threshold $t$, as $\theta$ tends to zero through positive values, the integral of the Gaussian CDF difference quotient converges to the Gaussian density at $t$ times the Gaussian expectation of $|Y|$.

**Proof.** Work under standard Gaussian measure, which is a probability measure. For each fixed $y$, the pointwise crossing quotient converges, as $\theta\to0^+$, to $\varphi(t)|y|$ (`rotated_gaussianCDF_quotient_tendsto`). For $0<\theta<1$, the quotient is bounded by $2\varphi(0)(|t|+|y|)$ (`rotated_gaussianCDF_quotient_le`). This dominating function is integrable: the constant term is integrable under a probability measure, and the identity function is integrable under a standard Gaussian law, hence so is its absolute value. The integrands are measurable, since the Gaussian CDF is continuous (`continuous_standardGaussianCDF`) and the remaining operations preserve continuity. The dominated convergence theorem for a filter then allows the limit to pass through the integral. The resulting limit is $\int \varphi(t)|y|\,d\gamma(y)=\varphi(t)\int |y|\,d\gamma(y)$.

**Key facts.** `BooleanAnalysis.GaussianSpace.rotated_gaussianCDF_quotient_tendsto`, `BooleanAnalysis.GaussianSpace.rotated_gaussianCDF_quotient_le`, `BooleanAnalysis.ThresholdFunctions.continuous_standardGaussianCDF`.
