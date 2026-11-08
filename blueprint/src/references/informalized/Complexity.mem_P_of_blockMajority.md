<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PClosure.lean :: Complexity.mem_P_of_blockMajority -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Block Majority Closure

**Claim.** For a language $V\in\mathsf{P}$ and the stated block and index bounds, the language where strictly more than half of the permitted indices yield pairs in $V$ belongs to $\mathsf{P}$.

**Proof.** First obtain a polynomial-time machine computing the indicator of $V$ from its membership in $\mathsf{P}$ (`Complexity.test_of_mem_P`). The block-majority test lemma (`Complexity.polyTimeComputable_blockMajorityTest`) uses this machine to compute the one-bit test for whether twice the number of successful indices exceeds the total number of indices. By `Complexity.mem_P_of_test`, the set on which that test is true belongs to $\mathsf{P}$. Unfolding the Boolean decision identifies this true set with the displayed strict-majority inequality.

**Key facts.** `Complexity.test_of_mem_P`, `Complexity.polyTimeComputable_blockMajorityTest`, `Complexity.mem_P_of_test`.
