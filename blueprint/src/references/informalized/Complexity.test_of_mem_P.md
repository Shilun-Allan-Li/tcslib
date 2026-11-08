<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PClosure.lean :: Complexity.test_of_mem_P -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Language Indicator

**Claim.** If a language $L$ of binary strings belongs to $\mathsf{P}$, then the function sending each binary string $z$ to the one-bit word indicating whether $z\in L$ is polynomial-time computable.

**Proof.** By the characterization of polynomial time as polynomial-time computability of the language indicator ( `mem_P_iff_polyTimeComputable` ), membership $L\in\mathsf P$ is equivalent to the required computability statement. Applying the forward implication to the given membership proves the claim.

**Key facts.** `Complexity.mem_P_iff_polyTimeComputable`.
