<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/GraphTheory/Kruskal/UnionFind.lean :: Kruskal.mergeAll_init_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial union-find reachability

**Claim.** Starting from the state in which each vertex represents itself and merging a list of edges in order gives equal representatives exactly for pairs connected by a path through that list.

**Proof.** Apply the reachability invariant for merging a list (`mergeAll_iff_reach`) with the empty list as the base. It remains to check its initial-state hypothesis: in the initial state, equal representatives mean that the two vertices are equal. Equality gives reflexive reachability through the empty list. Conversely, a path through the empty list can only be reflexive, so its endpoints are equal. With this hypothesis established, the invariant identifies equality of representatives after merging the given edges with reachability through the empty list concatenated with those edges, which is just reachability through the given list.

**Key facts.** `Kruskal.mergeAll_iff_reach`.
