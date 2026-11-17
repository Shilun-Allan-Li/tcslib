<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Classes.lean :: Randomized.randProb_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegativity of Random-String Probability

**Claim.** For any natural number $m$ and any decidable property $A$ of Boolean strings, the probability that a uniformly random Boolean string of length $m$ satisfies $A$ is nonnegative.

**Proof.** The probability is the number of satisfying words divided by $2^m$. The numerator is a cardinality and hence nonnegative, and the denominator is positive. Therefore the quotient is nonnegative.
