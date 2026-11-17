<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/GraphTheory/Kruskal/UnionFind.lean :: Kruskal.mergeAll_iff_reach -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Merging preserves reachability

**Claim.** If a union-find state records exactly the reachability relation through a base edge list, then after folding another list of edges into that state, equality of representatives is equivalent to reachability through the concatenated list.

**Proof.** Induct on the list of edges to be merged, allowing both the starting state and base list to vary. For the empty list, the claim is the assumed correspondence between equal representatives and reachability through the base. For a list beginning with edge $e$, first merge its endpoints, then apply the induction hypothesis with the enlarged base consisting of the old base followed by $e$. The merge changes representatives by joining the two components containing the endpoints of $e$. Accordingly, two vertices have equal representatives after this merge exactly when they were already connected through the base, or their base components can be joined using $e$. The characterization of paths using a leading edge (`reach_cons_iff`), together with symmetry of reachability (`reach_symm`) and the fact that enlarging an edge list preserves paths (`reach_mono`), identifies precisely these possibilities with reachability through the enlarged base. This proves the induction step, and hence the result for the full list.

**Key facts.** `Kruskal.reach_cons_iff`, `Kruskal.reach_mono`, `Kruskal.reach_symm`.
