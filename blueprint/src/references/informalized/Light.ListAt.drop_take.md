<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/ArrayAt.lean :: Light.ListAt.drop_take -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Restricting a List Segment

**Claim.** Dropping the first $k$ entries of a list that records a consecutive segment, then taking the next $n$ entries, gives a list of length $n$ recording the segment starting at $a+k$, with its endpoint still at most $\mathrm{top}$.

**Proof.** The segment property is preserved first under dropping entries: the remaining list records the values starting at $a+k$ (`Seg.drop`). Taking its first $n$ entries preserves that same recording property (`Seg.take`). For the length, dropping $k$ from a list of length $N$ leaves length $N-k$, and taking $n$ gives length $n$ because $k+n\le N$. Finally, the original bound $a+N\le\mathrm{top}$ and $k+n\le N$ imply $(a+k)+n\le\mathrm{top}$.

**Key facts.** `Light.Seg.drop`, `Light.Seg.take`.
