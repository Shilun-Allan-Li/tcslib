<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PClosure.lean :: Complexity.mem_P_of_blockAny -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Block Search Closure

**Claim.** For a language $V\in\mathsf{P}$ and the stated block and index bounds, the language of inputs for which some permitted block yields an encoded pair in $V$ belongs to $\mathsf{P}$.

**Proof.** Convert the assumption $V\in\mathsf{P}$ into a polynomial-time machine computing its one-bit indicator (`Complexity.test_of_mem_P`). The block-search test lemma (`Complexity.polyTimeComputable_blockAnyTest`) then gives a polynomial-time computation of the bit that is true exactly when at least one index in the prescribed range produces a pair in $V$. Turning a polynomial-time Boolean test into its true-set language preserves membership in $\mathsf{P}$ (`Complexity.mem_P_of_test`). The remaining set equality identifies the test's existential condition with the stated one: a true indicator means the corresponding pair belongs to $V$, and conversely membership makes that indicator true.

**Key facts.** `Complexity.test_of_mem_P`, `Complexity.polyTimeComputable_blockAnyTest`, `Complexity.mem_P_of_test`.
