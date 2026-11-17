<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/Basic.lean :: BooleanAnalysis.ThresholdFunctions.expect_const_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Homogeneity of Uniform Expectation

**Claim.** For every dimension, scalar, and real-valued function on the Boolean cube, the uniform expectation of the function multiplied pointwise by the scalar is the scalar times the function's uniform expectation.

**Proof.** Expanding expectation gives the uniform weight multiplied by the finite sum of the pointwise scalar multiples. Pulling the scalar out of this finite sum leaves the product of the scalar, the uniform weight, and the sum of the function values. Associativity and commutativity of real multiplication identify this with the scalar times the original expectation.
