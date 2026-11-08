<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/DualityMeasurePreserving.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.volume_zVariable_dualProtocol_dualZValue -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Duality Preserves Fiber Mass

**Claim.** The fiber over the dual value for the dual protocol has the same ambient measure as the fiber over the original achievable value.

**Proof.** Write $S$ for the dual fiber. Since the dual-sample map preserves volume, the measure of the preimage of $S$ equals the measure of $S$ (`volume_measurePreserving_dualHardSample`). The preimage identity for dual fibers says that this preimage is precisely the original fiber (`zVariable_dualProtocol_preimage_dualZValue`). Applying the measure to these equal sets proves the result.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.volume_measurePreserving_dualHardSample`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.zVariable_dualProtocol_preimage_dualZValue`.
