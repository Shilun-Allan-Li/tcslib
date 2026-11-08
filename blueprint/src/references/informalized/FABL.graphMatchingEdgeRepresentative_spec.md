<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.graphMatchingEdgeRepresentative_spec -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Representative of a Matching Edge

**Claim.** For any perfect matching and any edge in that matching, the chosen representative vertex maps to that same edge under the matching’s vertex-to-edge correspondence.

**Proof.** By definition, the representative is chosen from the fiber of the vertex-to-edge map over the given edge, using the surjectivity of that map for a perfect matching. The specification of the chosen preimage therefore says exactly that its image is the original edge.
