<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/ZFiberMeasure.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.zFiberMeasure_cond_specialYFalse_eq_disjointSpecialYFalseMeasure_cond_zVariable -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Equality of iterated conditional measures

**Claim.** Conditioning the hard-distribution measure on the fiber $Z=z$ and then on Bob's special bit being false gives the same measure as first conditioning on disjointness and that bit being false, then conditioning on $Z=z$.

**Proof.** First, conditioning the measure on the fiber $Z=z$ and then on the event that the special bit is false is equivalent to conditioning the original hard-distribution measure on the intersection of those two events (`zFiberMeasure_cond_specialY_eq_volume_cond_inter`). Reordering the intersection puts the special-bit event first. The measure conditioned on disjointness and the special bit being false, then conditioned on the fiber, is also the disjoint-conditioned measure conditioned on this same intersection (`disjointSpecialYFalseMeasure_cond_zVariable_eq_cond_inter`). Finally, every sample in the intersection has special bit false, and therefore belongs to the disjoint event (`mem_disjointEvent_of_specialY_eq_false`). On any subset of the disjoint event, conditioning the original measure agrees with conditioning the disjoint-conditioned measure (`volume_cond_eq_disjointCondMeasure_cond_of_subset_disjointEvent`). These identifications show the two iterated conditional measures are equal.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.zFiberMeasure_cond_specialY_eq_volume_cond_inter`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.disjointSpecialYFalseMeasure_cond_zVariable_eq_cond_inter`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.mem_disjointEvent_of_specialY_eq_false`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.volume_cond_eq_disjointCondMeasure_cond_of_subset_disjointEvent`.
