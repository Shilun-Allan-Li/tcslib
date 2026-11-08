<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise/HypercontractivePairing.lean :: BooleanAnalysis.GaussianSpace.gaussianNoise_dual_test_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Dual Test Bound for Gaussian Noise

**Claim.** Under the stated exponent, correlation, marginal-preservation, and integrability hypotheses, the absolute value of the Gaussian integral pairing of the noise image of $f$ with $g$ is bounded by the product of the indicated $L^p$ seminorms.

**Proof.** Set $r=(q-1)^{-1}$ and $s=p-1$. The assumptions imply $r,s>0$, $rs\le1$, and $\rho^2\le rs$, with $0\le\rho\le1$. The exponent identities $1+r=q/(q-1)$ and $1+s=p$ put $g$ and $f$ in the spaces required by the two-function Gaussian inequality. That inequality ($\texttt{gaussian_two_function_positiveOffsets}$), together with the given measure-preserving marginals, ensures integrability of the correlated product and bounds the integral of $|g(z_1)||f(z_2)|$ by the product of their corresponding seminorms. The correlated-measure integral formula ($\texttt{integral_correlatedGaussianMeasure_of_integrable}$) rewrites the pairing in the claim as the integral of $g(z_1)f(z_2)$ over the correlated pair (up to swapping factors). The absolute value of an integral is at most the integral of the absolute value; applying this and then the two-function bound yields the stated estimate. The exponent identities convert the resulting seminorms to precisely those displayed in the claim.

**Key facts.** `BooleanAnalysis.GaussianSpace.gaussian_two_function_positiveOffsets`, `BooleanAnalysis.GaussianSpace.integral_correlatedGaussianMeasure_of_integrable`.
