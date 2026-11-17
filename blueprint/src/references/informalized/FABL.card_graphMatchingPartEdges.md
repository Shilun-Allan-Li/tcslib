<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.card_graphMatchingPartEdges -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Matching edges at a part

**Claim.** In a perfect matching of the complete multipartite graph with $k$ vertices in each part, exactly $k$ matching edges have an endpoint in any specified part.

**Proof.** The matching edges incident to the specified part are in bijection, via the matching's part-edge correspondence, with the $k$ positions in that part. Consequently their finite cardinalities agree, so there are exactly $k$ such edges.
