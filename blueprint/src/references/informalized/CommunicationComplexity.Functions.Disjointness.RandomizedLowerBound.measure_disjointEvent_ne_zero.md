<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/HardDistributionEvents.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.measure_disjointEvent_ne_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Disjointness Event Has Positive Measure

**Claim.** The event that Alice’s and Bob’s input sets are disjoint has nonzero ambient measure.

**Proof.** The measure of the disjointness event is $3/4$ (`measureReal_disjointEvent`). In particular, its real-valued measure is nonzero. For a measure value in the extended nonnegative reals, nonzero real-valued measure implies the original measure is nonzero; applying this implication proves the claim.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.measureReal_disjointEvent`.
