<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.graphMatchingPartEdge_injective -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Injectivity of the Partwise Edge Map

**Claim.** For a fixed part, distinct positions determine distinct edges of the perfect matching containing the corresponding vertices.

**Proof.** Suppose two positions in the fixed part map to the same matching edge. The matching property for the vertex-to-edge map says that the two corresponding vertices are either equal or adjacent in the matching. In the first case, equality of the vertices gives equality of their positions. In the second case, adjacency in the complete multipartite graph forces their parts to differ; but both vertices lie in the fixed part, a contradiction. Therefore the positions are equal, proving injectivity.

**Key facts.** `FABL.matching_eq_or_adj_of_toEdge_eq`.
