<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/GraphTheory/Kruskal/UnionFind.lean :: Kruskal.mergeAll_preserves -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Merging Preserves Existing Components

**Claim.** If two nodes have the same representative before a sequence of edge merges, they still have the same representative afterward.

**Proof.** Induct on the edge list, allowing the initial state and the two nodes to vary. The empty list leaves the state unchanged, so the assumed equality of representatives gives the result. In the step, merge the first edge’s endpoints. This operation replaces representatives in the component of one endpoint by the other endpoint’s representative, and leaves all other representatives unchanged. Thus two nodes that previously had equal representatives still have equal representatives after this merge; apply the induction hypothesis to the remaining edges.
