<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/FuncIndexing/Basic.lean :: CommunicationComplexity.Functions.Indexing.oneWayCommunicationComplexity_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Index Complexity Upper Bound

**Claim.** For every positive integer $n$, the deterministic one-way communication complexity of the Index function on $n$-bit inputs is at most $n$.

**Proof.** Consider the protocol in which Alice sends her entire $n$-bit input and Bob returns the bit at his requested coordinate. This protocol computes Index exactly. Its message set consists of all Boolean strings of length $n$, so it has $2^n$ messages and costs $n$ bits. The characterization `communicationComplexity_le_iff` says that exhibiting an exact protocol with cost at most $n$ proves the claimed upper bound.

**Key facts.** `CommunicationComplexity.Deterministic.OneWay.communicationComplexity_le_iff`.
