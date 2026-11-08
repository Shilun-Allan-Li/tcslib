<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/DualHardSample.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.bobClaimConditioning_dualHardSample -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Duality of conditioning variables

**Claim.** Under reversal of coordinate order and exchange of Alice’s and Bob’s roles, Bob’s conditioning variable on the dual sample is the reversed and exchanged recoding of Alice’s conditioning variable on the original sample.

**Proof.** The two vector components of Bob’s conditioning variable on the dual sample are identified by the duality identities: Alice’s bits through the special coordinate become the reversal of Bob’s bits from that coordinate onward (`xLeSpecial_dualHardSample`), and Bob’s bits strictly after it become the reversal of Alice’s bits strictly before it (`yAfterSpecial_dualHardSample`). The special coordinate itself becomes its reversed index under the dual sample. Substituting these three component identities into the definitions of the conditioning variables gives the claimed equality.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.xLeSpecial_dualHardSample`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.yAfterSpecial_dualHardSample`.
