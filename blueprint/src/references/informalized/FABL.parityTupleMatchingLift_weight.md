<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.parityTupleMatchingLift_weight -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier weight preservation under the lift

**Claim.** The product of the absolute Fourier coefficients indexed by the lifted matching labels equals the product indexed by the original tuple of subsets.

**Proof.** Fix a part of the tuple. The set of labels on the vertices in that part is exactly the original subset, by \(FABL.LevelKParityTuple.matchingLabelSet_assignedVertexLabel\). Thus the Fourier coefficient indexed by that label set equals the coefficient indexed by the original subset, and their absolute values agree. Multiplying these equalities over all parts gives equality of the two Fourier weights.

**Key facts.** `FABL.LevelKParityTuple.matchingLabelSet_assignedVertexLabel`.
