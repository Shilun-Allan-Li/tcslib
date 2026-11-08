<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/HardDistributionEvents.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.disjointSpecialYFalseMeasure_isProbabilityMeasure -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Probability of the Doubly Conditioned Law

**Claim.** The measure obtained by conditioning the hard distribution first on disjointness and then on Bob’s special bit being false has total mass one.

**Proof.** First, the disjointness event has positive ambient measure (\texttt{measure_disjointEvent_ne_zero}), so conditioning the ambient probability measure on that event produces a probability measure. Next, under this disjointness-conditioned law, the event that Bob’s special bit is false has real measure $2/3$ (\texttt{disjointCondMeasure_measureReal_specialY_false}), which is positive. Conditioning once more on this event therefore again gives a probability measure, as claimed.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.measure_disjointEvent_ne_zero`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.disjointCondMeasure_measureReal_specialY_false`.
