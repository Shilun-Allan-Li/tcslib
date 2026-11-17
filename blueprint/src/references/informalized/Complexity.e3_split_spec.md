<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.e3_split_spec -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Soundness of the split search

**Claim.** If the exponential split search at length $m$ returns $n$, then $n\le m$ and $n+C\cdot 2^{(n+1)^c}=m$.

**Proof.** A successful result of `List.find?` must be an element of the searched list, so $n$ belongs to `List.range (m+1)` and hence $n<m+1$, which for natural numbers gives $n\le m$. The same successful search result certifies that the Boolean test is true. Since the test is the decidable equality in the claim, this gives $n+C\cdot 2^{(n+1)^c}=m$.
