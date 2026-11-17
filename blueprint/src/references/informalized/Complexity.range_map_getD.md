<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PAdviceSubsetPPoly.lean :: Complexity.range_map_getD -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Range Map Gives the Prefix

**Claim.** If $n\le |z|$, mapping the indices $0,\ldots,n-1$ to the corresponding bits of $z$, with false as the default, gives exactly the prefix of $z$ of length $n$.

**Proof.** The two lists have the same length: the mapped range has length $n$, and the prefix has length $n$ because $n\le |z|$. To identify their entries, fix any index $i<n$. The entry of the mapped list at $i$ is the value of the mapping function at the $i$th element of the range, which is $i$ itself. Since $i<n\le |z|$, this is an in-range index of $z$, so its defaulted lookup agrees with the actual $i$th bit. The prefix has that same bit at index $i$. Thus the lists agree at every valid index and have equal length, so they are equal.
