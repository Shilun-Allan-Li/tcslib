<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/HardDistributionEvents.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.mem_disjointEvent_of_specialY_eq_false -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bob’s Special Bit Being False Ensures Disjointness

**Claim.** If Bob’s special-coordinate bit is false, then the input sets determined by the sample are disjoint.

**Proof.** For a hard sample, disjointness of the two input sets is equivalent to the special bits not both being true (`disjoint_X_Y_iff`). Since Bob’s special bit is false, the conjunction that both special bits are true cannot hold. The equivalence therefore gives disjointness.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.disjoint_X_Y_iff`.
