<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/HardDistributionEvents.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.disjointCondMeasure_ae_disjointEvent -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Support of the conditioned measure

**Claim.** Under the distribution conditioned on disjointness, Alice’s and Bob’s input sets are disjoint almost surely.

**Proof.** By definition, the conditioned measure is the original measure restricted to the disjointness event. A basic property of conditioning a measure on an event is that the conditioning event has full measure under the resulting measure. Applying this property to the event that the two input sets are disjoint gives the asserted almost-sure statement.
