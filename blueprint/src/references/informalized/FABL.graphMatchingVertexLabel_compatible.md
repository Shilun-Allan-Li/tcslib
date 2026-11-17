<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.graphMatchingVertexLabel_compatible -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Compatibility of Vertex Labels

**Claim.** If each vertex receives the label assigned to its matching edge, then the endpoints of every matching edge have equal labels.

**Proof.** Take adjacent vertices in the matching. The matching’s vertex-to-edge correspondence sends both endpoints to the same edge, by the fact that adjacent vertices have equal images under this correspondence. The vertex label is the edge assignment evaluated at that image, so the two labels are equal.
