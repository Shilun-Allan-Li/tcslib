<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Util/List.lean :: List.getD_flatMap_finRange -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lookup in equal-length concatenations

**Claim.** If each list assigned to an index below $n$ has length $k$, then the entry at position $ik+r$ in their concatenation is the entry at position $r$ in the list assigned to $i$, for $i<n$ and $r<k$, with the same default.

**Proof.** First rewrite the concatenation over `finRange n` as a concatenation over `range n`: mapping each bounded index to its underlying natural number turns `finRange n` into `range n` (`List.map_coe_finRange_eq_range`). The summand at a natural number $z<n$ is the list assigned to the bounded index $z$; outside this range it is empty. The equal-length lookup theorem for a range concatenation (`List.getD_flatMap_range`) now identifies position $ik+r$ with the $r$th entry of the list at $i$.

**Key facts.** `List.map_coe_finRange_eq_range`, `List.getD_flatMap_range`.
