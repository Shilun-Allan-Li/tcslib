<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/AliceYFalse.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.volume_measurePreserving_flipSpecialX -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Flipping preserves volume

**Claim.** Toggling Alice's special-coordinate bit is measurable and preserves the volume measure on hard samples.

**Proof.** Every map on this finite discrete space is measurable. It remains to show that the pushforward measure agrees with volume. Equality of measures can be checked on singletons, and the preimage of a singleton under the flip is the singleton containing the flipped sample (`flipSpecialX_preimage_singleton`). That singleton has the same volume mass as the original one (`volume_measureReal_singleton_flipSpecialX`). Thus the pushforward and volume agree on all singletons, proving measure preservation.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.flipSpecialX_preimage_singleton`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.volume_measureReal_singleton_flipSpecialX`.
