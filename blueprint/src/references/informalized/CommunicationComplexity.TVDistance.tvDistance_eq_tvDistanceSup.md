<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/TVDistance.lean :: CommunicationComplexity.TVDistance.tvDistance_eq_tvDistanceSup -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Event-Supremum Characterization of Total Variation

**Claim.** The total variation distance between probability measures equals the supremum, over measurable events, of the absolute difference between the probabilities they assign to the event.

**Proof.** Let r be the total variation distance in its half-mass form. The bound on event differences (`event_abs_measureReal_sub_le_half_totalVariation`) says every measurable event has absolute probability difference at most r. Since r is nonnegative, it is an upper bound for the set of all such differences, and hence their supremum is at most r. Conversely, the Hahn-decomposition attainment result (`exists_event_abs_measureReal_sub_eq_half_totalVariation`) supplies a measurable event whose absolute difference is exactly r. The supremum is therefore at least r as well, proving equality.

**Key facts.** `CommunicationComplexity.TVDistance.event_abs_measureReal_sub_le_half_totalVariation`, `CommunicationComplexity.TVDistance.exists_event_abs_measureReal_sub_eq_half_totalVariation`.
