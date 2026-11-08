<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/UPathWalk.lean :: Complexity.LogProg.sum_slots -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Average over Padded Edge Slots

**Claim.** For each vertex, averaging over the padded slot range with out-of-range slots contributing zero gives the same value as averaging over all edge slots at that vertex.

**Proof.** The padded degree is defined to be $2^{\mathrm{Nat.size}(n)}$, so its rational value is exactly the denominator in the left-hand average. The range from $0$ to $2^{\mathrm{Nat.size}(n)}-1$ indexes precisely the elements of the finite type of that size. In the summand, an in-range index selects the corresponding neighbor slot, while the conditional contributes zero for an index outside the padded degree; here the padded degree equals the range size, so every index is in range. Reindexing this finite sum by the slot type identifies it with the sum over all slots in the graph's degree. The denominators are equal, and hence the averages agree.
