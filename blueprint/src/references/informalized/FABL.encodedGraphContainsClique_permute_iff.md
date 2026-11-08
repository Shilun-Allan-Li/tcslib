<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/GraphPropertyExamples.lean :: FABL.encodedGraphContainsClique_permute_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Clique Existence Under Vertex Relabeling

**Claim.** A relabeled graph contains a clique of size $k$ if and only if the original graph contains a clique of size $k$.

**Proof.** Suppose the relabeled graph has a clique on a vertex set $S$ of size $k$. Map $S$ back by the inverse permutation. A bijection preserves the set's cardinality. For any two distinct vertices of this preimage, their images lie in $S$ and are distinct, so the clique property in the relabeled graph makes them adjacent there. The adjacency-under-relabeling equivalence (`encodedGraphAdjacent_permute_iff`) then gives adjacency of the original vertices in the original graph. This produces a size-$k$ clique in the original graph. Conversely, map a size-$k$ clique in the original graph forward by the permutation. Its cardinality is unchanged, and any two distinct vertices in the image have distinct preimages in the original clique. Their original adjacency transfers to adjacency in the relabeled graph by the same equivalence. Thus the image is a size-$k$ clique.

**Key facts.** `FABL.encodedGraphAdjacent_permute_iff`.
