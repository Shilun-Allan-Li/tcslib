<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/GraphTheory/Kruskal/Optimality.lean :: Kruskal.kruskal_spans -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Connectivity of Kruskal’s output

**Claim.** For every pair of vertices connected by a path through $E$, there is also a path between them through the edges selected by Kruskal’s algorithm on $E$.

**Proof.** Sort $E$ by weight. Since sorting preserves membership, every edge of $E$ occurs in this sorted list, so reachability through $E$ implies reachability through the sorted list by monotonicity of reachability (`reach_mono`). The processing theorem `processEdges_same_partition` says that merging all selected edges after processing the sorted list induces the same partition as merging all edges of the sorted list. For the initial union-find state, equality of representatives is equivalent to reachability through the corresponding edge list (`mergeAll_init_iff`). Thus a path through the sorted list gives equal representatives after merging all its edges; the equal-partition result transfers this equality to the selected edges, and the same equivalence yields a path through Kruskal’s output.

**Key facts.** `Kruskal.reach_mono`, `Kruskal.processEdges_same_partition`, `Kruskal.mergeAll_init_iff`.
