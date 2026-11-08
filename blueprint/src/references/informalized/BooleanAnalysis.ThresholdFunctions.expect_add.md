<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/Basic.lean :: BooleanAnalysis.ThresholdFunctions.expect_add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Additivity of Uniform Expectation

**Claim.** For every dimension and real-valued functions on the Boolean cube, the uniform expectation of their pointwise sum is the sum of their uniform expectations.

**Proof.** By definition, expectation is the uniform weight multiplied by the sum of the function over all cube points. The finite sum of a pointwise sum splits into the sum of the two finite sums, and distributivity of multiplication over addition then gives the claimed identity.
