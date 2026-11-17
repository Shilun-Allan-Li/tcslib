<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/DualityMeasurePreserving.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.volume_measureReal_zVariable_dualProtocol_dualZValue -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Dualization preserves fiber volume

**Claim.** For any protocol and achievable $Z$-value, the fiber of its dual value under the dual protocol has the same real volume as the original fiber.

**Proof.** Real-valued mass is obtained by taking the real part of the measure of a set. The underlying volume measures of the two fibers are equal by the fiber-preservation result for dual protocols and dual $Z$-values (`volume_zVariable_dualProtocol_dualZValue`). Taking real-valued mass on both sides gives the claimed equality.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.volume_zVariable_dualProtocol_dualZValue`.
