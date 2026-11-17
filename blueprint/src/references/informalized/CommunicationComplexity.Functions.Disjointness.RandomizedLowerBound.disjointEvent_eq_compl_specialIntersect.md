<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/HardDistributionEvents.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.disjointEvent_eq_compl_specialIntersect -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Disjointness and special intersection

**Claim.** The disjointness event is the complement of the event that both special bits are true.

**Proof.** For each sample, disjointness of the input sets is equivalent to the negation of the condition that both special bits are true (`disjoint_X_Y_iff`). This pointwise equivalence says exactly that the disjointness event is the complement of the special-intersection event.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.disjoint_X_Y_iff`.
