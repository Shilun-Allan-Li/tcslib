<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/FuncIndexing/Basic.lean :: CommunicationComplexity.Functions.Indexing.oneWayCommunicationComplexity_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exact Index Complexity

**Claim.** For every positive integer $n$, the deterministic one-way communication complexity of the Index function on $n$-bit inputs is exactly $n$.

**Proof.** The upper-bound result `oneWayCommunicationComplexity_le` gives complexity at most $n$, while `le_oneWayCommunicationComplexity` gives complexity at least $n$. Antisymmetry of the order on extended natural numbers therefore yields equality.

**Key facts.** `CommunicationComplexity.Functions.Indexing.oneWayCommunicationComplexity_le`, `CommunicationComplexity.Functions.Indexing.le_oneWayCommunicationComplexity`.
