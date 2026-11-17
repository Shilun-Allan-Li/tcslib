<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/GraphPropertyExamples.lean :: FABL.encodedGraphConnected_permute_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Connectivity Under Vertex Relabeling

**Claim.** An encoded graph is connected if and only if the graph obtained by permuting its vertices is connected.

**Proof.** First suppose the relabeled graph is connected. Given original vertices $u,w$, connectedness supplies a path in the relabeled graph from their images under the permutation. Pull this path back vertex by vertex using the inverse permutation. Each adjacent step remains adjacent after the pullback, by the adjacency-under-relabeling equivalence (`encodedGraphAdjacent_permute_iff`). The pulled-back path joins $u$ to $w$, proving the original graph connected. Conversely, suppose the original graph is connected. For any vertices in the relabeled graph, take their preimages under the permutation and a path between those preimages in the original graph. Push the path forward along the permutation; the same adjacency equivalence ensures every step is an edge of the relabeled graph. Hence the relabeled graph is connected.

**Key facts.** `FABL.encodedGraphAdjacent_permute_iff`.
