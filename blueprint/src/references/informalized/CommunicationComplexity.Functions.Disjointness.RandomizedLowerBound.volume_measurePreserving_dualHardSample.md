<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/DualityMeasurePreserving.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.volume_measurePreserving_dualHardSample -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Dualization preserves volume

**Claim.** The dualization map is measurable and pushes the uniform volume measure on hard samples to itself.

**Proof.** On the finite discrete sample space, every map is measurable. To prove that the pushforward measure equals volume, it suffices to compare their masses on each singleton. For a sample $\omega$, the preimage of $\{\omega\}$ under dualization is the singleton containing its dual (`dualHardSample_preimage_singleton`). The mass of that singleton equals the mass of $\{\omega\}$ (`volume_measureReal_singleton_dualHardSample`). Hence the pushforward and volume agree on every singleton, and therefore are equal.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.dualHardSample_preimage_singleton`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.volume_measureReal_singleton_dualHardSample`.
