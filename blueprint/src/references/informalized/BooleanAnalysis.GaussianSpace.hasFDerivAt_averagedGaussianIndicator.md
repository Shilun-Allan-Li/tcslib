<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/IndicatorRegularity.lean :: BooleanAnalysis.GaussianSpace.hasFDerivAt_averagedGaussianIndicator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Derivative of an averaged Gaussian indicator

**Claim.** Let $n\in\mathbb N$, let $A\subseteq\mathbb R^n$ be measurable, and let $u$ satisfy $\sin u\ne0$. The Gaussian average $F(x)=\int 1_A(\cos u\,x+\sin u\,y)\,d\gamma_n(y)$ is differentiable at every $x$. Its derivative is the integral of the indicator against the derivative of the product Gaussian density in its mean vector, evaluated at $\cos u\,x$, composed with multiplication by $\cos u$.

**Proof.** Write $v=\sin^2u$, which is strictly positive because $\sin u\ne0$. The averaged indicator can be expressed as an integral over Lebesgue measure of $1_A(z)$ times the product Gaussian density with mean vector $c=\cos u\,x$ and variance $v$ (\texttt{averagedGaussianIndicator\_eq\_integral\_density}). As a function of its mean vector, the integral of this density against the bounded measurable function $1_A$ is differentiable, and its derivative is the integral of $1_A$ against the derivative of the product density (\texttt{hasFDerivAt\_integral\_gaussianProductDensity}). Finally, the mean vector depends linearly on $x$ by coordinatewise multiplication by $\cos u$; the chain rule composes the integral's derivative with this linear map, yielding the asserted derivative.

**Key facts.** `BooleanAnalysis.GaussianSpace.averagedGaussianIndicator_eq_integral_density`, `BooleanAnalysis.GaussianSpace.hasFDerivAt_integral_gaussianProductDensity`.
