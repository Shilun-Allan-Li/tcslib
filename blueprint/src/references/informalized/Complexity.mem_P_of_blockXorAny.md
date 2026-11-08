<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PClosure.lean :: Complexity.mem_P_of_blockXorAny -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Block XOR Search Closure

**Claim.** For $V\in\mathsf{P}$ and the stated nested pair decoding, block length, and search bound, the language where some permitted block gives an XOR-modified pair in $V$ belongs to $\mathsf{P}$.

**Proof.** From $V\in\mathsf{P}$ obtain a polynomial-time machine for its one-bit indicator (`Complexity.test_of_mem_P`). The block-XOR search test lemma (`Complexity.polyTimeComputable_blockXorAnyTest`) then computes in polynomial time whether some index in the prescribed range makes the encoded pair, with the second component formed by the specified listwise XOR, belong to $V$. The true set of any polynomial-time Boolean test is in $\mathsf{P}$ (`Complexity.mem_P_of_test`). Unfolding the test's finite-range search proves that this true set is exactly the language in the claim: indicator value true is equivalent to membership in $V$.

**Key facts.** `Complexity.test_of_mem_P`, `Complexity.polyTimeComputable_blockXorAnyTest`, `Complexity.mem_P_of_test`.
