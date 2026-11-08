<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/GraphTheory/Kruskal/Optimality.lean :: Kruskal.processEdges_optimal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Optimality of the Greedy Edge Sweep

**Claim.** For a nondecreasingly weighted edge list, the sweep’s selected edges have total weight at most that of any sublist of the input whose merges induce the same partition as merging the entire input, assuming the initial state represents reachability through the base edges.

**Proof.** Proceed by induction on the sorted input list, generalizing the initial state, base graph, and comparison list. The empty input is immediate. For a first edge $e$, distinguish whether its endpoints are already in the same component.

1. If they are already connected, the sweep skips $e$. The reduction lemma (`Kruskal.reduce_to_rest`) removes the need for $e$ from the comparison list while preserving its spanning property and producing a comparison list drawn from the remaining edges with no greater weight. The skip identity (`Kruskal.processEdges_skip`) and the induction hypothesis on the tail then give the desired bound.

2. If the endpoints are in different components and $e$ belongs to the comparison list $S$, the sweep takes $e$. Reorder $S$ to put $e$ last, using permutation invariance of merging (`Kruskal.mergeAll_perm`), and use the fact that merging a list can be viewed as merging its first edge before its tail (`Kruskal.mergeAll_cons_eq`). Since the two endpoints of $e$ are merged together, this shows that after merging $e$ into the initial state, the remaining edges of $S$ still span the same partition as the tail. The reachability characterization after merges (`Kruskal.mergeAll_iff_reach`) supplies the updated base hypothesis for induction. The erase-weight identity (`Kruskal.totalWeight_erase`) accounts for removing $e$ from $S$, and the sweep’s take-weight identity (`Kruskal.processEdges_take_weight`) accounts for its contribution to the greedy total. Combining these gives the bound.

3. If the endpoints are different but $e$ is absent from $S$, the spanning hypothesis implies that its endpoints become connected after merging $S$. The exchange lemma (`Kruskal.uf_exchange`) therefore supplies an edge $f$ of $S$ whose removal, after first merging $e$, preserves the partition. Since $e$ is absent from $S$ and $S$ is drawn from the input, $f$ lies in the tail. Apply the reduction lemma to obtain a comparison list from the tail that still spans after merging $e$ and whose weight is no greater than that of $S$ with $f$ removed. Use reachability after merges to update the induction hypothesis. Finally, the sortedness hypothesis gives $e.weight \le f.weight$; together with the erase-weight identity and the sweep’s take-weight identity, this shows that replacing $f$ by $e$ does not increase the comparison cost and proves the bound.

**Key facts.** `Kruskal.processEdges_skip`, `Kruskal.reduce_to_rest`, `Kruskal.mergeAll_perm`, `Kruskal.mergeAll_cons_eq`, `Kruskal.mergeAll_iff_reach`, `Kruskal.totalWeight_erase`, `Kruskal.processEdges_take_weight`, `Kruskal.uf_exchange`.
