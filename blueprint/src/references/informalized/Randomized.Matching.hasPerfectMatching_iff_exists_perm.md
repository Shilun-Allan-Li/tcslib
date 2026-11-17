<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/MatchingMath.lean :: Randomized.Matching.hasPerfectMatching_iff_exists_perm -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Perfect Matchings and Permutations

**Claim.** The bipartite graph determined by $A$ has a perfect matching if and only if there is a permutation $\sigma$ of the indices such that $A_{i,\sigma(i)}$ is true for every $i$.

**Proof.** Suppose first that a subgraph is a perfect matching. The characterization of perfect matchings says every vertex has exactly one matching neighbor. Each left vertex therefore has a right neighbor: its unique neighbor cannot be on the left, since the bipartite graph has no edges between two left vertices. Choose this right neighbor and call it $f(i)$. If $f(i)=f(i')$, the right vertex has the same unique matching neighbor in both cases; symmetry of matching adjacency then forces $i=i'$. Thus $f$ is injective, hence bijective on the finite set of indices, and so defines a permutation $\sigma$. Since the matching is a subgraph of the original graph, each chosen edge is an edge of that graph, giving $A_{i,\sigma(i)}=\mathrm{true}$. Conversely, suppose such a permutation exists. Form the graph whose only edges pair each left vertex $i$ with the right vertex $\sigma(i)$. The assumed matrix entries ensure these edges occur in the original graph. Every left vertex has exactly its designated right neighbor, and every right vertex $j$ has exactly the left neighbor $\sigma^{-1}(j)$; there are no same-side edges. Hence this subgraph is a perfect matching.

**Key facts.** `Randomized.Matching.not_bipartiteGraph_adj_inl_inl`, `Randomized.Matching.not_bipartiteGraph_adj_inr_inr`.
