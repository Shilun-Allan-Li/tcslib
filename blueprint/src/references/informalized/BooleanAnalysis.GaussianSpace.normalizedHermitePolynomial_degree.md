<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Hermite/Degree.lean :: BooleanAnalysis.GaussianSpace.normalizedHermitePolynomial_degree -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Degree of a normalized Hermite polynomial

**Claim.** For every nonnegative integer $k$, the normalized Hermite polynomial of degree $k$ has degree $k$.

**Proof.** The factorial $k!$ is positive, so its real square root is positive and its reciprocal is nonzero. Multiplying a polynomial by a nonzero constant does not change its degree. Also, mapping the integer-coefficient Hermite polynomial into $[?]$ preserves its degree because its leading coefficient remains nonzero. The Hermite polynomial of degree $k$ has degree $k$, hence so does the normalized polynomial.
