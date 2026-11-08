<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/Polynomial.lean :: BooleanAnalysis.ThresholdFunctions.MultilinearPolynomial.sum_sq_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positive sum of squared coefficients

**Claim.** If a real coefficient family is nonzero, then the sum of the squares of all its coefficients is strictly positive.

**Proof.** Because the family is nonzero, some coefficient $p(S)$ is nonzero. Every term $p(T)^2$ in the finite sum is nonnegative, and the selected term $p(S)^2$ is strictly positive. Hence the whole sum is strictly positive.
