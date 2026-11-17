<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/RectangleSwitching.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.yAfterSpecial_eq_of_same_zVariable -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Post-special Bits Determined by the Record

**Claim.** If two hard samples yield the same achievable value $z$ of the transcript, special coordinate, Alice’s preceding bits, and Bob’s following bits, then their Bob-after-special vectors are equal.

**Proof.** Each sample’s Bob-after-special vector is determined by its value of $Z$: when a sample maps to $z$, its vector equals the $yAfter$ component of $z$ (`yAfterSpecial_eq_of_zVariable_eq`). Apply this fact to both samples. Both vectors equal the same component $z.yAfter$, so they are equal by transitivity of equality.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.yAfterSpecial_eq_of_zVariable_eq`.
