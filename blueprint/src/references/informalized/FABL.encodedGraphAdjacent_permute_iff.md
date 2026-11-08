<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/GraphPropertyExamples.lean :: FABL.encodedGraphAdjacent_permute_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Adjacency Under Vertex Relabeling

**Claim.** Relabeling the vertices of an encoded graph by a permutation preserves adjacency: the permuted vertices are adjacent in the relabeled graph exactly when the original vertices are adjacent in the original graph.

**Proof.** For the forward implication, take an edge witnessing adjacency of the permuted vertices. Pull that edge back along the vertex permutation. The relabeled graph assigns it the same Boolean value as the original graph assigns to the corresponding original edge, and membership of each permuted vertex in the witness edge pulls back to membership of its original vertex. Distinctness also pulls back, since a permutation is injective. For the reverse implication, push an edge witnessing adjacency of the original vertices forward along the permutation. Its Boolean value in the relabeled graph is the original edge's value, and its endpoints are the permuted vertices; injectivity again preserves distinctness. Thus each direction transports the edge witness along the induced equivalence on two-element vertex subsets.
