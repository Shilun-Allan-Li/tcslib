<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Hermite/Noise.lean :: BooleanAnalysis.GaussianSpace.integral_normalizedHermite_affine_standardGaussian -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Affine Averaging of Normalized Hermite Polynomials

**Claim.** If $\rho^2+s^2=1$, then for every natural number $k$ and real $x$, averaging the normalized degree-$k$ Hermite polynomial at $\rho x+sy$ over standard Gaussian $y$ gives $\rho^k$ times that polynomial evaluated at $x$.

**Proof.** Use the affine averaging identity for the unnormalized degree-$k$ Hermite polynomial: its average at $\rho x+sy$ is $\rho^k$ times its value at $x$. The normalized Hermite polynomial is this polynomial multiplied by the constant $(k!)^{-1/2}$. Pull that constant through the integral and multiply the affine averaging identity by it; the result is precisely the claimed formula.

**Key facts.** `BooleanAnalysis.GaussianSpace.integral_hermite_affine_standardGaussian`.
