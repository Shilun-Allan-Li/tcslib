<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/DualityMeasurePreserving.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.inputDist_measureReal_eq_preimage -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input probability as a preimage measure

**Claim.** For any set of input pairs, its probability under the hard input distribution equals the hard-sample measure of its preimage under the input map.

**Proof.** The hard input measure is defined as the pushforward of the hard-sample measure by the map taking a sample to its input pair. Therefore, the measure of a set of input pairs under this pushforward is the measure of its preimage under that map. Taking real-valued measures on both sides gives the asserted equality.
