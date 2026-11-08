<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Bobkov.lean :: BooleanAnalysis.GaussianSpace.bobkovFunctional_zero_dim -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bobkov Functional in Dimension Zero

**Claim.** For every real-valued function on the zero-dimensional Boolean cube, its Bobkov functional equals the closed Gaussian profile evaluated at its expectation.

**Proof.** The zero-dimensional Boolean cube has just one point, so its uniform expectation is the value of $f$ there. The derivative sum is empty, and the expectation defining the Bobkov functional therefore reduces to the square root of the square of the profile at that value. The profile is nonnegative (`closedGaussianProfile_nonneg`), so this square root is the profile itself.

**Key facts.** `BooleanAnalysis.GaussianSpace.closedGaussianProfile_nonneg`.
