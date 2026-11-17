<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Hermite/Basis.lean :: BooleanAnalysis.GaussianSpace.gaussianPolynomialLp_hermite -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Hermite Polynomial in Gaussian L²

**Claim.** For every nonnegative integer $n$ and multi-index $\alpha:\{1,\ldots,n\}\to\mathbb N$, the Gaussian $L^2$ image of the multivariate Hermite polynomial indexed by $\alpha$ is the $L^2$ class of its Hermite function.

**Proof.** By definition, the Gaussian polynomial map sends a polynomial to the $L^2$ class of its evaluation function. For the multivariate Hermite polynomial, that evaluation function is exactly the Hermite function indexed by $\alpha$. The definition of $\mathrm{hermiteL2}(\alpha)$ is this same $L^2$ class, so the two elements agree by unfolding the definitions.
