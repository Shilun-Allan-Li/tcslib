<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/GraphTheory/Kruskal/UnionFind.lean :: Kruskal.mergeAll_congr -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Merge folds preserve partitions

**Claim.** If two union-find states induce the same partition, then folding the same edge list into each state produces states that still induce the same partition.

**Proof.** Induct on the edge list, keeping both starting states arbitrary subject to inducing the same partition. For the empty list, the claim is the assumed equality of partitions. For a list beginning with an edge $e$, merge the endpoints of $e$ into both states. These two resulting states still induce the same partition: each merge identifies precisely the elements in the component of one endpoint with those in the component of the other, and the original states have the same component relation. Apply the induction hypothesis to these merged states and the remaining edges.
