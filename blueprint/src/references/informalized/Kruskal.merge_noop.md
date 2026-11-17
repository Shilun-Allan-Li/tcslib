<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/GraphTheory/Kruskal/UnionFind.lean :: Kruskal.merge_noop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Merging Within One Component Does Nothing

**Claim.** If two nodes already have the same representative, merging their components leaves the union-find state unchanged.

**Proof.** Evaluate the merged state at an arbitrary node $k$. The merge changes its representative only if the representative of $k$ equals that of the second endpoint. Since the two endpoints have equal representatives, the replacement representative is that same value. In either case, the value at $k$ is unchanged, so the two states agree at every node.
