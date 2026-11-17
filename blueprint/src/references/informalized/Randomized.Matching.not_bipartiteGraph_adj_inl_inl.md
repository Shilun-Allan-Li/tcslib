<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/MatchingMath.lean :: Randomized.Matching.not_bipartiteGraph_adj_inl_inl -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# No Edges Within the Left Part

**Claim.** For any Boolean matrix $A$ and indices $i,j$, the left-part vertices indexed by $i$ and $j$ are not adjacent in the bipartite graph specified by $A$.

**Proof.** By the definition of the graph, adjacency is false for every pair of vertices whose two entries both lie in the left part. Thus the proposed adjacency is impossible.
