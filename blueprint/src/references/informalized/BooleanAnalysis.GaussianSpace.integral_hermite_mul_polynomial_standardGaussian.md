<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Hermite/Orthogonality.lean :: BooleanAnalysis.GaussianSpace.integral_hermite_mul_polynomial_standardGaussian -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Hermite Integrals and Derivatives

**Claim.** For every natural number $k$ and real polynomial $p$, the standard Gaussian integral of the degree-$k$ Hermite polynomial times $p$ equals the standard Gaussian integral of the $k$th derivative of $p$.

**Proof.** We induct on $k$, allowing the polynomial $p$ to vary at each induction step. For $k=0$, the degree-zero Hermite polynomial is $1$ and the zeroth iterate of differentiation is the identity, so both integrands agree. For the successor step, the Hermite integration-by-parts identity says that the integral involving the degree-$(k+1)$ Hermite polynomial and $p$ equals the integral involving the degree-$k$ Hermite polynomial and $p'$. Apply the induction hypothesis to $p'	skip$, obtaining the integral of the $k$th derivative of $p'$. This is the $(k+1)$st iterated derivative of $p$, as required.

**Key facts.** `BooleanAnalysis.GaussianSpace.integral_hermite_succ_mul_polynomial_standardGaussian`.
