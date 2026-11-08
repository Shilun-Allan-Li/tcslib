<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/ProductDifferentiation.lean :: BooleanAnalysis.GaussianSpace.hasFDerivAt_integral_gaussianProductDensity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Differentiating a Gaussian product average

**Claim.** For a finite set $I$, positive variance $v$, and measurable $f\colon\mathbb R^I\to\mathbb R$ with $|f(z)|\le 1$, the Gaussian product average as a function of its mean is Fréchet differentiable at every $c$. Its derivative is the integral of $f(z)$ times the mean derivative of the product density.

**Proof.** Choose an integrable dominating function that bounds both the product Gaussian density and its mean derivative whenever the mean lies in the ball of radius $1$ about $c$; the Gaussian domination result provides such a function (\texttt{gaussianProductDensity\_derivative\_dominated}). In that ball, each coordinate of the mean is bounded by $\|c\|+1$, using the coordinate bound for points in a ball (\texttt{abs\_coordinate\_le\_of\_mem\_ball}). Since $|f|\le1$, multiplication by $f$ preserves these bounds. The integrand is measurable because the Gaussian density is measurable in each coordinate and $f$ is measurable. Its derivative with respect to the mean is obtained by differentiating the product density and multiplying by the fixed factor $f(z)$; the pointwise derivative is supplied by \texttt{hasFDerivAt\_gaussianProductDensity}. The candidate derivative is measurable because the mean derivative of the density depends continuously on its mean (\texttt{continuous\_gaussianProductDensityDerivative}). Thus the dominated differentiation theorem for parameter-dependent integrals applies, giving the stated derivative as the integral of the pointwise derivative.

**Key facts.** `BooleanAnalysis.GaussianSpace.gaussianProductDensity_derivative_dominated`, `BooleanAnalysis.GaussianSpace.abs_coordinate_le_of_mem_ball`, `BooleanAnalysis.GaussianSpace.hasFDerivAt_gaussianProductDensity`, `BooleanAnalysis.GaussianSpace.continuous_gaussianProductDensityDerivative`.
