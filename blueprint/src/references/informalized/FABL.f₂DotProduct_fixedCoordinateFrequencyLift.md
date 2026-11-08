<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/RestrictedWeightAlgorithm.lean :: FABL.f₂DotProduct_fixedCoordinateFrequencyLift -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pairing with a Fixed-Coordinate Lift

**Claim.** The dot product of the fixed-coordinate frequency lift of γ with x equals the dot product of γ with the restriction of x to the complement of J.

**Proof.** The lift is defined by applying the inverse of the dot-product linear equivalence to the functional obtained by composing γ's dot-product functional with the coordinate projection. The defining evaluation identity for this equivalence says that pairing the lifted vector with x recovers that composed functional evaluated at x. Evaluating the composition gives the dot product of γ with the projection of x, as claimed.
