<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/DualHardSample.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.input_mix -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input of a mixed sample

**Claim.** When the two samples agree on the specified special coordinate and the indicated portions of their Alice and Bob bit vectors, the mixed sample has Alice's input set from the first sample and Bob's input set from the second.

**Proof.** The mixed sample's Alice input set equals that of the first sample under the stated agreement hypotheses (`X_mix`). Its Bob input set equals that of the second sample under the same hypotheses (`Y_mix`). Since the input is the ordered pair of these two sets, the asserted identity follows.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.X_mix`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.Y_mix`.
