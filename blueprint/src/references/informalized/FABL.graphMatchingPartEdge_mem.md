<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.graphMatchingPartEdge_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Matching Edge Incident to a Part

**Claim.** The matching edge containing the vertex at a given position in a fixed part belongs to the set of matching edges incident to that part.

**Proof.** Membership in the set of matching edges incident to a part is characterized by the existence of a position in that part whose vertex is an endpoint of the edge. Take the given position. The vertex-to-edge correspondence sends its vertex to the matching edge containing it, so that vertex is an endpoint of the resulting edge. This establishes the required membership.

**Key facts.** `FABL.mem_graphMatchingPartEdges_iff`.
