<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.graphMatchingLabelingToEdgeAssignment_leftInverse -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recovering Edge Assignments from Labelings

**Claim.** Converting a labeling induced by a matching and its edge assignment back to an edge assignment recovers both the matching and every edge label.

**Proof.** Start with a matching and an assignment of labels to its edges. The conversion back uses the same matching, so the matching components agree immediately. For any edge, the recovered label is the vertex label at the chosen representative of that edge. By construction, that vertex label is the assignment evaluated at the edge obtained by mapping the representative through the matching’s vertex-to-edge correspondence. The representative specification says this image is the original edge, so the recovered label equals its assigned label. Thus both components are recovered.

**Key facts.** `FABL.graphMatchingEdgeRepresentative_spec`.
