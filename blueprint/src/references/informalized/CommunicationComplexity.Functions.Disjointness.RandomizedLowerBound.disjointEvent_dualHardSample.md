<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/DualHardSample.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.disjointEvent_dualHardSample -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Duality preserves disjointness

**Claim.** A sample is in the disjointness event if and only if its dual sample is in that event.

**Proof.** For any sample, disjointness is equivalent to the special bits not both being true (`disjoint_X_Y_iff`). Duality exchanges these two bits, and exchanging their order does not change whether both are true. Thus the original and dual samples satisfy the same disjointness condition.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.disjoint_X_Y_iff`.
