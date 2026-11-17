<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/Basic.lean :: BooleanAnalysis.ThresholdFunctions.expect_sub -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Subtraction and Expectation

**Claim.** The uniform expectation of the pointwise difference of two functions equals the difference of their uniform expectations.

**Proof.** Write the pointwise difference as a sum with a negated second function. Linearity of expectation gives the expectation of that sum as the sum of the expectations (`expect_add`); compatibility with negation identifies the second term as the negative of the expectation of the original function (`expect_neg`). This is the stated difference.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.expect_add`, `BooleanAnalysis.ThresholdFunctions.expect_neg`.
