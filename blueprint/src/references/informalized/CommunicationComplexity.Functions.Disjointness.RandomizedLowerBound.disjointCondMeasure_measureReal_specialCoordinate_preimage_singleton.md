<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/HardDistributionEvents.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.disjointCondMeasure_measureReal_specialCoordinate_preimage_singleton -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniformity of the special coordinate

**Claim.** Under disjointness conditioning, the probability that the special coordinate equals any specified index is $1/n$.

**Proof.** The preimage of the singleton containing the specified index under the special-coordinate map is exactly the event that the sample’s special coordinate equals that index (`specialCoordinate_preimage_singleton`). The conditioned measure of this event is $1/n$ (`disjointCondMeasure_measureReal_specialCoordinateEvent`), yielding the claim.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.specialCoordinate_preimage_singleton`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.disjointCondMeasure_measureReal_specialCoordinateEvent`.
