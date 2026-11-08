<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise/Kernel.lean :: BooleanAnalysis.GaussianSpace.integral_correlatedGaussianMeasure_of_integrable -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Correlated Gaussian integral formula

**Claim.** Whenever $(x,y)\mapsto f(x)g(y)$ is integrable under the correlated Gaussian law with parameter $\rho$, its integral equals the integral under $\gamma_n$ of $f(x)$ times the Gaussian noise average of $g$ at $x$.

**Proof.** Let $C(x,w)=(x,\rho x+\sqrt{1-\rho^2}\,w)$, with the operations taken coordinatewise. By definition, the correlated Gaussian measure is the image of $\gamma_n\times\gamma_n$ under $C$. The change of variables formula for an integrable function under a measure-preserving map therefore rewrites the left-hand integral as the integral of $f(x)g(\rho x+\sqrt{1-\rho^2}w)$ over the product measure. Fubini's theorem expresses this as an iterated integral, first in $w$ and then in $x$. The inner integral is precisely the Gaussian noise average of $g$ at $x$, giving the result.
