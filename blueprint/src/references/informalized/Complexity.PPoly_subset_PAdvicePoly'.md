<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PPolyAdvice.lean :: Complexity.PPoly_subset_PAdvicePoly' -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Circuit languages have polynomial advice algorithms

**Claim.** Every language in the polynomial-circuit class belongs to the polynomial advice class, with the advice length and running-time bounds specified in the statement.

**Proof.** This is the set-theoretic restatement of the preceding inclusion: the class of polynomial-circuit languages is defined as the set of languages having polynomial circuit size, and `Complexity.PPoly_subset_PAdvicePoly` places every such language in the polynomial advice class.

**Key facts.** `Complexity.PPoly_subset_PAdvicePoly`.
