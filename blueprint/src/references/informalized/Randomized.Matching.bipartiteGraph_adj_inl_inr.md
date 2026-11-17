<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/MatchingMath.lean :: Randomized.Matching.bipartiteGraph_adj_inl_inr -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Adjacency from Left to Right

**Claim.** For each Boolean matrix $A$ and indices $i,j\in\mathrm{Fin}(n)$, the left vertex indexed by $i$ is adjacent to the right vertex indexed by $j$ exactly when $A_{ij}=\mathrm{true}$.

**Proof.** By the definition of the associated bipartite graph, adjacency from a left vertex to a right vertex is defined to be the equality $A_{ij}=\mathrm{true}$. The two sides of the equivalence are therefore identical.
