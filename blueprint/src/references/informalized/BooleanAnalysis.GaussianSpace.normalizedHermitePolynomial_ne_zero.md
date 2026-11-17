<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Hermite/Degree.lean :: BooleanAnalysis.GaussianSpace.normalizedHermitePolynomial_ne_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonvanishing of normalized Hermite polynomials

**Claim.** For every nonnegative integer $k$, the normalized Hermite polynomial of degree $k$ is nonzero.

**Proof.** Suppose it were the zero polynomial. The zero polynomial has degree bottom, whereas the degree theorem gives this polynomial degree $k$, which is a natural number and hence not bottom. This contradiction proves nonvanishing; the degree theorem used here is BooleanAnalysis.GaussianSpace.normalizedHermitePolynomial_degree.

**Key facts.** `BooleanAnalysis.GaussianSpace.normalizedHermitePolynomial_degree`.
