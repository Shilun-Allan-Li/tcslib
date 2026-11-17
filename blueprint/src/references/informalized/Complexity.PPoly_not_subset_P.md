<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UHaltMachine.lean :: Complexity.PPoly_not_subset_P -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial circuits exceed polynomial time

**Claim.** There is a language recognized by a polynomial-size, fan-in-two circuit family that is not decidable in polynomial time.

**Proof.** Suppose every polynomial-circuit language were in $	extsf{P}$. Since every language in $	extsf{P}$ is in $	extsf{EXP}$ (`Complexity.P_subset_EXP`), this would imply that every polynomial-circuit language is in $	extsf{EXP}$. That contradicts the separation theorem `Complexity.PPoly_not_subset_EXP`.

**Key facts.** `Complexity.PPoly_not_subset_EXP`, `Complexity.P_subset_EXP`.
