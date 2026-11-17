<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/DualityMeasurePreserving.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.disjointCondMeasure_measurePreserving_dualHardSample -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Dual invariance of the conditioned distribution

**Claim.** The map that reverses coordinates and swaps Alice’s and Bob’s roles preserves the disjoint-conditioned measure.

**Proof.** The sample space is finite with the discrete measurable structure, so the dual map is measurable. To verify preservation of measure, it suffices to compare the measures of singleton sets. For any sample $\omega$, the preimage of the singleton containing $\omega$ under the dual map is exactly the singleton containing its dual (dual-preimage-of-singleton identity, `dualHardSample_preimage_singleton`). The two singleton masses are equal under the conditioned measure (`disjointCondMeasure_measureReal_singleton_dualHardSample`). Thus the pushforward and original measures agree on every singleton, and hence on all sets in this finite space.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.dualHardSample_preimage_singleton`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.disjointCondMeasure_measureReal_singleton_dualHardSample`.
