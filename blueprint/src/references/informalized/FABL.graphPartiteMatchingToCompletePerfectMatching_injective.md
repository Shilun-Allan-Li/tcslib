<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.graphPartiteMatchingToCompletePerfectMatching_injective -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Injectivity of the Matching Relabeling

**Claim.** For any $r$ and $k$, relabeling a perfect matching in the complete multipartite graph with $2r$ parts of size $k$ as a perfect matching on $2rk$ vertices is injective.

**Proof.** Suppose two matchings have the same relabeled matching. Their underlying subgraphs in the complete graph are equal. To show the original partite subgraphs are equal, first note that both have all vertices: this follows from the vertex coverage in the perfect-matching property. Their adjacency relations are also equal. Indeed, transport the equality of relabeled adjacency back along the vertex equivalence from partite vertices to the numbered vertices; the relabeling definition identifies these adjacencies exactly. Thus the original subgraphs agree, and their matching subtype elements are equal.
