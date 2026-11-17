<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/ZFiberMeasure.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.xDistance_dualProtocol_dualZValue_eq_yDistance -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Duality Exchanges Conditional Bit Distances

**Claim.** Alice’s special-bit distance from uniform for the dual protocol and dual record equals Bob’s special-bit distance from uniform for the original protocol and record.

**Proof.** By definition, each distance is the total variation distance between the corresponding conditional special-bit law and the uniform bit law. The conditional-law identity for dualization (`conditionalSpecialXLaw_dualProtocol_dualZValue`) identifies Alice’s law in the dual system with Bob’s law in the original system. Substituting this equality into the distance definitions gives the result.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.conditionalSpecialXLaw_dualProtocol_dualZValue`.
