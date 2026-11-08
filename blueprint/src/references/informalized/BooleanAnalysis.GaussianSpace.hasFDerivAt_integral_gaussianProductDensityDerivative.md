<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/ProductHessian.lean :: BooleanAnalysis.GaussianSpace.hasFDerivAt_integral_gaussianProductDensityDerivative -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Differentiating the integrated density derivative

**Claim.** For a finite set $I$, positive variance $v$, and measurable $f\colon\mathbb R^I\to\mathbb R$ with $|f(z)|\le1$, the integral of $f(z)$ times the mean derivative of the product Gaussian density is Fréchet differentiable in the mean at every $c$. Its derivative is the integral of $f(z)$ times the Hessian of the product density.

**Proof.** Take an integrable bound for the norm of the product-density Hessian, uniform for means whose coordinates are bounded by $\|c\|+1$; this is provided by the Hessian domination result (\texttt{gaussianProductDensityHessian\_dominated}). Points in the radius-$1$ ball about $c$ satisfy that coordinate bound (\texttt{abs\_coordinate\_le\_of\_mem\_ball}), and $|f|\le1$ means the same integrable bound controls the norm after multiplication by $f$. The integrand is measurable: the mean derivative is continuous in its mean, and the Hessian is jointly continuous in the mean and integration variable (\texttt{continuous\_gaussianProductDensityDerivative}, \texttt{continuous\_gaussianProductDensityHessian\_joint}). At each fixed integration point, differentiating the mean derivative gives the Hessian, so the pointwise derivative of the integrand is $f(z)$ times that Hessian (\texttt{hasFDerivAt\_gaussianProductDensityDerivative}). The integrand at $c$ is integrable by the established integrability result (\texttt{integrable\_gaussianProductDensityDerivative\_smul}). The dominated differentiation theorem now yields the claimed derivative of the integral.

**Key facts.** `BooleanAnalysis.GaussianSpace.gaussianProductDensityHessian_dominated`, `BooleanAnalysis.GaussianSpace.abs_coordinate_le_of_mem_ball`, `BooleanAnalysis.GaussianSpace.continuous_gaussianProductDensityDerivative`, `BooleanAnalysis.GaussianSpace.continuous_gaussianProductDensityHessian_joint`, `BooleanAnalysis.GaussianSpace.hasFDerivAt_gaussianProductDensityDerivative`, `BooleanAnalysis.GaussianSpace.integrable_gaussianProductDensityDerivative_smul`.
