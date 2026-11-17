<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/Basic.lean :: BooleanAnalysis.ThresholdFunctions.expect_const -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expectation of a Constant

**Claim.** For every dimension and real number, the uniform expectation of the constant function with that value is the value itself.

**Proof.** Rewrite uniform expectation as the expectation operator for the uniform distribution on the finite cube (BooleanAnalysis.expect_eq_fintypeExpect). The expectation of a constant random variable on a probability space is that constant (Fintype.expect_const).

**Key facts.** `BooleanAnalysis.expect_eq_fintypeExpect`.
