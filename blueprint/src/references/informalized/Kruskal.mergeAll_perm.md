<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/GraphTheory/Kruskal/UnionFind.lean :: Kruskal.mergeAll_perm -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Permutation Invariance of Edge Merging

**Claim.** If two lists of weighted edges are permutations of one another, merging each list into the same initial union-find state yields states that induce the same partition of the nodes.

**Proof.** Induct on the list-permutation proof. The empty-list case compares the initial state with itself, so the partitions agree. Adding the same edge to both lists preserves partition agreement by the fact that applying the same sequence of merges to states with the same partition preserves that agreement (`Kruskal.mergeAll_congr`). For the swap step, exchanging two adjacent edges does not change the induced partition after those two merges (`Kruskal.merge_swap_partition`); applying the remaining merges preserves this agreement. Finally, for a composite of two permutations, compose the corresponding partition equivalences using transitivity of having the same partition (`Kruskal.UF.SamePartition.trans`).

**Key facts.** `Kruskal.mergeAll_congr`, `Kruskal.merge_swap_partition`, `Kruskal.UF.SamePartition.trans`.
