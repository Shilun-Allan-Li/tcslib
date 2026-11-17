<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.graphMatchingEdgeAssignmentToLabeling_weight -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Factorization of Matching Fourier Weight

**Claim.** The Fourier weight of the induced vertex labeling equals the product of the Fourier factors indexed by the parts.

**Proof.** Write the edge assignment as a matching together with its labels. For each part, the label set used by the induced vertex labeling is exactly the image of the positions in that part under the edge assignment along their matching edges. Consequently, the absolute Fourier coefficient appearing in the weight at that part is the corresponding edge Fourier factor. This identifies the two products factor by factor.
