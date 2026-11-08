<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PAdviceSubsetPPoly.lean :: Complexity.PPoly_eq_PAdvicePoly -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Circuit Size Equals Polynomial Advice Time

**Claim.** The class of Boolean languages recognized by polynomial-size fan-in-two circuit families equals the class decidable in polynomial time by a Turing machine given polynomially bounded advice.

**Proof.** The proof establishes the two inclusions separately. First, every language with polynomial circuit size belongs to the polynomial advice-time class, by the circuit-to-advice simulation (\texttt{Complexity.PPoly_subset_PAdvicePoly}). In the other direction, every language decidable in polynomial time with polynomially bounded advice belongs to the polynomial circuit-size class, by the advice-to-circuit simulation (\texttt{Complexity.PAdvicePoly_subset_PPoly}). Since the set of languages with the stated circuit property is precisely the circuit class, these inclusions give the asserted equality.

**Key facts.** `Complexity.PPoly_subset_PAdvicePoly`, `Complexity.PAdvicePoly_subset_PPoly`.
