<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PolyTimeBlockLoop.lean :: Complexity.flatMap_range_eq_single -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Singleton contribution to a range flat map

**Claim.** If $K<N$ and the list assigned at each index below $N$ is $b$ at $K$ and empty elsewhere, then the flat map of the first $N$ indices is $b$.

**Proof.** Induct on $N$. The case $N=0$ is impossible under $K<N$. For the successor case, split according to whether the last index $N$ is $K$. If they are equal, every earlier index differs from $K$, so its assigned list is empty; hence the flat map over the earlier range is empty. The last list is $b$, and adjoining it gives the result. If $N\ne K$, then $K<N$; apply the induction hypothesis to the earlier range. The list assigned at the new last index is empty, so appending it leaves the flat map unchanged.
