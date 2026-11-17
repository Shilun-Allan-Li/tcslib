<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/ZFiberMeasure.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.volume_zVariable_dualProtocol_dualZValue_inter_specialX -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Dual Special-Bit Fiber Mass

**Claim.** For each bit $b$, the dual fiber restricted to samples whose special Alice bit is $b$ has the same ambient mass as the original fiber restricted to samples whose special Bob bit is $b$.

**Proof.** Let $S$ be the dual fiber intersected with the event that the special Alice bit is $b$. The dual-sample map preserves volume, so $S$ and its preimage have equal measure (`volume_measurePreserving_dualHardSample`). The preimage identity for this restricted fiber identifies that preimage exactly with the original fiber intersected with the event that the special Bob bit is $b$ (`dualHardSample_preimage_zVariable_dualZValue_inter_specialX`). Taking measures of these equal sets gives the claimed equality.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.dualHardSample_preimage_zVariable_dualZValue_inter_specialX`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.volume_measurePreserving_dualHardSample`.
