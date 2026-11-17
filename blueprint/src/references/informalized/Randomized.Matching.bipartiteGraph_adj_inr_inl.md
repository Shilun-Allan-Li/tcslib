<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/MatchingMath.lean :: Randomized.Matching.bipartiteGraph_adj_inr_inl -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Adjacency from Right to Left

**Claim.** For each Boolean matrix $A$ and indices $i,j\in\mathrm{Fin}(n)$, the right vertex indexed by $j$ is adjacent to the left vertex indexed by $i$ exactly when $A_{ij}=\mathrm{true}$.

**Proof.** In the definition of the associated bipartite graph, adjacency from a right vertex indexed by $j$ to a left vertex indexed by $i$ is exactly the condition $A_{ij}=\mathrm{true}$. Hence the stated equivalence follows directly from the definition.
