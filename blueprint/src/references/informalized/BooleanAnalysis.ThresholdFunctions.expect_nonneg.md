<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/Basic.lean :: BooleanAnalysis.ThresholdFunctions.expect_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegativity of Uniform Expectation

**Claim.** If a function on the Boolean cube is nonnegative at every point, then its uniform expectation is nonnegative.

**Proof.** Rewrite the uniform expectation as the finite-type expectation using `expect_eq_fintypeExpect`. The expectation of a pointwise nonnegative function over a finite probability space is nonnegative, so the result follows.

**Key facts.** `BooleanAnalysis.expect_eq_fintypeExpect`.
