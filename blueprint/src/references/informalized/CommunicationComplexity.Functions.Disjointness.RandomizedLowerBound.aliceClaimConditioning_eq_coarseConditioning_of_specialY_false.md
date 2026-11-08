<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/AliceYFalse.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.aliceClaimConditioning_eq_coarseConditioning_of_specialY_false -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Conditioning Agreement at a False Special Bit

**Claim.** If Bob’s bit at the special coordinate is false, Alice’s corrected conditioning triple equals the coarse conditioning triple.

**Proof.** The first two components of the triples are the same by definition. For the last component, the weak suffix $Y_{\ge T}$ differs from the strict suffix $Y_{>T}$ only possibly at $T$. The identity `yGeSpecial_eq_yAfterSpecial_of_specialY_false` says that when Bob’s special bit is false, these two padded vectors coincide. Hence all three components agree.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.yGeSpecial_eq_yAfterSpecial_of_specialY_false`.
