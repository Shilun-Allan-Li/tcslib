<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PClosure.lean :: Complexity.lenLe_mem_P -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decoded length comparison is polynomial-time decidable

**Claim.** For a binary string $z$, the language where the second total decoded component has length at most the first has membership in $\mathsf{P}$.

**Proof.** The Boolean test that returns true exactly when the second total decoded component has length at most the first is polynomial-time computable (`Complexity.polyTimeComputable_lenLe`). The theorem that the true set of a polynomial-time computable Boolean test belongs to $\mathsf{P}$ (`Complexity.mem_P_of_test`) applies directly. This true set is the language specified in the claim.

**Key facts.** `Complexity.polyTimeComputable_lenLe`, `Complexity.mem_P_of_test`.
