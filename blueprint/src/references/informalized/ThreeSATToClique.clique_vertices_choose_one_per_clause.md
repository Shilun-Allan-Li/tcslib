<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/NPReductions/ThreeSATToClique.lean :: ThreeSATToClique.clique_vertices_choose_one_per_clause -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One clique vertex per clause

**Claim.** If a clique in the conflict graph has as many vertices as the formula has clauses, then for every clause index there is exactly one clique vertex with that clause index.

**Proof.** On the clique, the map sending a vertex to its clause index is injective: if two clique vertices had the same clause index, they could not be adjacent, whereas distinct vertices of a clique must be adjacent. Therefore the image of the clique has the same cardinality as the clique, namely the number of clauses. It is a subset of the set of all clause indices, which has that same finite cardinality, so it is the entire set of clause indices. Every index is consequently attained, and injectivity makes its preimage unique.
