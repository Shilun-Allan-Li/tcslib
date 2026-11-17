<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Hermite/Degree.lean :: BooleanAnalysis.GaussianSpace.normalizedHermitePolynomial_natDegree -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Natural degree of a normalized Hermite polynomial

**Claim.** For every nonnegative integer $k$, the normalized Hermite polynomial of degree $k$ has natural degree $k$.

**Proof.** Its degree, viewed in the natural numbers with an added bottom element to account for the zero polynomial, is $k$ by the degree theorem for normalized Hermite polynomials (BooleanAnalysis.GaussianSpace.normalizedHermitePolynomial_degree). Since this degree is the natural number $k$, the polynomial is nonzero, and its natural degree agrees with $k$.

**Key facts.** `BooleanAnalysis.GaussianSpace.normalizedHermitePolynomial_degree`.
