<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/PolynomialThresholdUniformStability.lean :: FABL.polynomialThresholdClass_closedUnderNegatingInputVariables -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Closure under negating input variables

**Claim.** For every natural number $k$, the class of Boolean functions admitting a polynomial threshold representation of Fourier degree at most $k$ is closed under negating input variables: multiplying each input coordinate by an assigned sign preserves membership in the class.

**Proof.** Take a function in the class and an assignment of signs to its coordinates. Negating the inputs according to this assignment is precisely the partition operation with that sign assignment and the identity coordinate map: both evaluate the original function at the coordinatewise signed input. The partition-function closure theorem preserves a polynomial threshold representation of Fourier degree at most $k$ (`isPolynomialThreshold_partitionFunction`), so the negated-input function remains in the class.

**Key facts.** `FABL.isPolynomialThreshold_partitionFunction`.
