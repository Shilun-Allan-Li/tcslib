<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/IndicatorRegularity.lean :: BooleanAnalysis.GaussianSpace.lipschitzWith_fderiv_averagedGaussianIndicator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lipschitz derivative of a Gaussian average

**Claim.** For measurable $A$ and $u$ with $\sin u\ne0$, the derivative of the Gaussian indicator average is Lipschitz with the stated constant $2n^2/\sin^2u$.

**Proof.** Let $v=\sin^2u$, which is positive because $\sin u\ne0$. The indicator of $A$ takes values between zero and one, so its absolute value is at most one. The product Gaussian density derivative estimate (`lipschitzWith_integral_gaussianProductDensityDerivative`) therefore makes the map that integrates this indicator against the mean derivative of the product density Lipschitz with constant $n^2(2/v)$. The derivative formula for the averaged indicator (`hasFDerivAt_averagedGaussianIndicator`) identifies its derivative at $x$ with this map evaluated at $\cos(u)x$, composed with the linear scaling $x\mapsto\cos(u)x$. This scaling has operator norm at most one. The contraction principle for Lipschitz maps (`lipschitzWith_comp_contraction`) preserves the same Lipschitz constant under this composition. Substituting $v=\sin^2u$ gives the stated constant.

**Key facts.** `BooleanAnalysis.GaussianSpace.lipschitzWith_integral_gaussianProductDensityDerivative`, `BooleanAnalysis.GaussianSpace.hasFDerivAt_averagedGaussianIndicator`, `BooleanAnalysis.GaussianSpace.lipschitzWith_comp_contraction`, `BooleanAnalysis.GaussianSpace.norm_cosineScaling_le_one`.
