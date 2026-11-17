<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/HardDistributionEvents.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.specialZeroZero_subset_disjointEvent -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero Special Bits Imply Disjointness

**Claim.** For every hard-distribution sample, if both special-coordinate bits are zero, then Alice’s and Bob’s input sets are disjoint; equivalently, the special-zero-zero event is contained in the disjointness event.

**Proof.** Take a sample in the special-zero-zero event. By the definition of that event, its Bob special bit is false. The fact that a false Bob special bit guarantees membership in the disjointness event ( `mem_disjointEvent_of_specialY_eq_false` ) therefore places the sample in the disjointness event. The condition on Alice’s special bit is not needed for this implication.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.mem_disjointEvent_of_specialY_eq_false`.
