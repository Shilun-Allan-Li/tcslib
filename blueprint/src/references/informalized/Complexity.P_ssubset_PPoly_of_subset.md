<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UHaltMachine.lean :: Complexity.P_ssubset_PPoly_of_subset -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Strict circuit containment from inclusion

**Claim.** If every language in $\mathsf{P}$ is decidable by a polynomial-size Boolean circuit family with fan-in at most two, then $\mathsf{P}$ is a proper subset of the class of all such circuit-decidable languages.

**Proof.** The assumed inclusion supplies one direction of containment. If the two classes were equal, then every language in the circuit class would belong to $\mathsf{P}$, contradicting the result that the circuit class is not contained in $\mathsf{P}$ (\texttt{Complexity.PPoly\_not\_subset\_P}). Hence the inclusion is strict.

**Key facts.** `Complexity.PPoly_not_subset_P`.
