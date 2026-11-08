<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Hermite/Orthogonality.lean :: BooleanAnalysis.GaussianSpace.integral_normalizedHermite_mul_standardGaussian -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Orthogonality of Normalized Hermite Polynomials

**Claim.** For all natural numbers $j,k$, the standard Gaussian integral of the product of the normalized degree-$j$ and degree-$k$ Hermite polynomials is $1$ if $j=k$ and $0$ otherwise.

**Proof.** Expand each normalized polynomial as its unnormalized Hermite polynomial multiplied by the reciprocal square root of its factorial. The unnormalized Hermite orthogonality identity says that the integral of their product is $j!$ when $j=k$ and zero otherwise. If $j\ne k$, the product of the normalization factors leaves zero. If $j=k$, the integral is $j!/(\sqrt{j!})^2=1$, since $j!>0$ and its square root is positive.

**Key facts.** `BooleanAnalysis.GaussianSpace.integral_hermite_mul_hermite_standardGaussian`.
