<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/IndicatorRegularity.lean :: BooleanAnalysis.GaussianSpace.norm_fderiv_averagedGaussianIndicator_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Derivative bound for a Gaussian indicator average

**Claim.** For a measurable set $A\subseteq\mathbb R^n$ and an angle $u$ with $\sin u\ne0$, the derivative of the Gaussian conditional indicator average at any point has norm at most $n\left(1+1/\sin^2u\right)$.

**Proof.** Set $v=\sin^2u$, viewed as a nonnegative real. The assumption that $\sin u$ is nonzero ensures $v\ne0$. The indicator of $A$ takes values only in $\{0,1\}$, so its absolute value is at most $1$ everywhere; it is measurable because $A$ is measurable. The derivative formula for the averaged Gaussian indicator (`hasFDerivAt_averagedGaussianIndicator`) expresses its derivative as an integral operator composed with cosine scaling. The operator norm of a composition is at most the product of the operator norms, and cosine scaling has norm at most $1$ (`norm_cosineScaling_le_one`). Finally, the bound for the integral of the Gaussian product-density derivative, applied to this bounded indicator and to $v\ne0$, gives $n(1+1/v)$. Since $v=\sin^2u$, this is the claimed bound.

**Key facts.** `BooleanAnalysis.GaussianSpace.hasFDerivAt_averagedGaussianIndicator`, `BooleanAnalysis.GaussianSpace.norm_cosineScaling_le_one`, `BooleanAnalysis.GaussianSpace.norm_integral_gaussianProductDensityDerivative_smul_le`.
