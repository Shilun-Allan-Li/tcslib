<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/DualHardSample.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.aliceClaimConditioning_dualHardSample -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Dual Conditioning Identity

**Claim.** For each hard sample, Alice’s corrected conditioning variable on its dual equals the dual recoding of Bob’s corrected conditioning variable on the original sample.

**Proof.** Expand Alice’s and Bob’s conditioning triples and the dual recoding. The first vector component agrees by the identity that Alice’s strict-prefix vector on the dual sample is the reversal of Bob’s strict-suffix vector on the original sample (`xBeforeSpecial_dualHardSample`). The second vector component agrees by the corresponding identity that Bob’s weak-suffix vector on the dual is the reversal of Alice’s weak-prefix vector (`yGeSpecial_dualHardSample`). The special coordinate is reversed on both sides by the definition of the dual sample, so the triples coincide.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.xBeforeSpecial_dualHardSample`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.yGeSpecial_dualHardSample`.
