<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/RectangleSwitching.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.xBeforeSpecial_eq_of_same_zVariable -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pre-Special Bits Agree on a Fiber

**Claim.** If two samples yield the same statistic value, then their padded vectors of Alice’s bits before the special coordinate are equal.

**Proof.** For each sample, the recovery property says that its before-special vector equals the before-special component of the shared statistic value (`xBeforeSpecial_eq_of_zVariable_eq`). The first sample’s vector therefore equals the second’s, by symmetry and transitivity of equality.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.xBeforeSpecial_eq_of_zVariable_eq`.
