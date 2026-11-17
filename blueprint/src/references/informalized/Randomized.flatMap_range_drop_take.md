<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/NPPoly.lean :: Randomized.flatMap_range_drop_take -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Extracting a block from a concatenation

**Claim.** If each list $g(j)$ for $j<K$ has length $c$, then for $i<K$ the length-$c$ block beginning at position $ic$ in the concatenation $g(0),\ldots,g(K-1)$ is exactly $g(i)$.

**Proof.** Proceed by induction on $K$. The case $K=0$ has no $i<K$. For $K+1$, split the concatenation into the first $K$ lists followed by $g(K)$; the first part has length $Kc$ (`length_flatMap_range`). If $i<K$, then the block from position $ic$ lies entirely within that first part, since $(i+1)c\le Kc$. Taking and then truncating the block therefore reduces to the induction hypothesis. If $i=K$, dropping the first $Kc$ entries removes the entire first part, leaving $g(K)$; taking its first $c$ entries returns all of $g(K)$ because its length is $c$.

**Key facts.** `Randomized.length_flatMap_range`.
