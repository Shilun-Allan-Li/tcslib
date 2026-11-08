<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFARM/Semantics.lean :: Complexity.LogProg.TQBFARM.drop_map_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mapping After Dropping a List Prefix

**Claim.** For $k<|q|$, mapping the bit-to-quantifier interpretation over the list obtained by dropping its first $k$ entries gives the quantifier for $q_k$, followed by the mapped list obtained by dropping its first $k+1$ entries.

**Proof.** Because $k<|q|$, the list obtained by dropping the first $k$ entries is nonempty, and its head is the original entry $q_k$. Decomposing that list into its head and tail, then mapping the bit-to-quantifier function over the decomposition, gives the quantifier for $q_k$ followed by the map over the list with the first $k+1$ entries dropped.
