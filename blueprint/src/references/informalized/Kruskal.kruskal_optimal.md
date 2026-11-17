<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/GraphTheory/Kruskal/Optimality.lean :: Kruskal.kruskal_optimal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Optimality of Kruskal’s algorithm

**Claim.** If $S$ is a sublist of the input edges $E$ and spans every connection present in $E$, then the total weight of Kruskal’s output on $E$ is at most the total weight of $S$.

**Proof.** Apply the optimality theorem for processing an already sorted edge list (`processEdges_optimal`) to the weight-sorted list obtained from $E$, with the initial union-find state and empty base list. Its invariant holds because initially two vertices have the same representative exactly when they are equal, which is exactly reachability through the empty list. Every edge of $S$ occurs in the sorted list, since it occurs in $E$ and sorting preserves membership. The required equality of final partitions follows by translating the initial-state partition into reachability: a path through the sorted list is a path through $E$, while a path through $S$ can be transferred to the sorted list because $S$ spans $E$ and every edge of $S$ occurs there. Finally, the sorted list is in nondecreasing order of weight: merge sort produces a sorted list for the weight comparison, which is transitive and total. These facts give the hypotheses of `processEdges_optimal`, and its conclusion is the asserted weight inequality.

**Key facts.** `Kruskal.processEdges_optimal`, `Kruskal.mergeAll_init_iff`, `Kruskal.reach_mono`.
