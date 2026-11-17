<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Util/List.lean :: List.getD_flatMap_range -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lookup in a range concatenation

**Claim.** When every list $f(z)$ for $z<n$ has length $k$, the entry at position $zk+r$ in the concatenation of those lists is the entry at position $r$ in $f(z)$, for $z<n$ and $r<k$, with the same default.

**Proof.** The total length of the lists before index $z$ is $zk$: the length-of-a-range-concatenation formula gives total length $nk$ (`List.length_flatMap_range`), and the same formula applied to the first $z$ lists gives $zk$. Thus position $zk+r$ is the offset $r$ within the block contributed by $f(z)$. The lookup theorem indexed by the sum of preceding list lengths makes this identification (`List.getD_flatMap_range_sum`); the constant length hypothesis turns that sum into $zk$, and $r<k$ ensures the requested entry lies in the block.

**Key facts.** `List.length_flatMap_range`, `List.getD_flatMap_range_sum`.
