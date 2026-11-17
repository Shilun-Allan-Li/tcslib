<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clRows_add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Concatenation of Row Streams

**Claim.** The packed stream of the first $n+m$ rows equals the stream of the first $n$ rows followed by the stream of the first $m$ rows of the family shifted by $n$.

**Proof.** Induct on $m$. When $m=0$, the claim follows because a stream of zero rows is empty. For the successor step, the recursive definition appends the packed row at the newest index to the stream of preceding rows. Apply the induction hypothesis to the preceding $n+m$ rows, then reassociate list concatenation; the newest row is exactly the next row of the shifted family. This yields the claimed decomposition for $m+1$.
