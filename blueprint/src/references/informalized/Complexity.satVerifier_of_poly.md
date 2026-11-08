<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satVerifier_of_poly -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-time verdict decides the verifier language

**Claim.** If the one-bit verifier verdict function is polynomial-time computable, then the language accepted by that verifier belongs to $\mathrm{P}$.

**Proof.** Unpack polynomial-time computability to obtain a machine and constants computing the one-bit verdict within the prescribed polynomial time. By the characterization of membership in $\mathrm{P}$ (`Complexity.mem_P_iff`), it suffices to show that this machine decides the verifier language within the corresponding bound. For each input, the one-bit word containing the verifier verdict equals the one-bit indicator of membership in that language, by the definition of the verifier language and of the indicator function. Therefore the machine's computed output is the required membership bit, with the same time bound.

**Key facts.** `Complexity.mem_P_iff`.
