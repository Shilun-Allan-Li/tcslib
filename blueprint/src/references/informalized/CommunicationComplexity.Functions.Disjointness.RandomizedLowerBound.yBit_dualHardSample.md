<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/DualHardSample.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.yBit_dualHardSample -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bob’s bit in the dual sample

**Claim.** At each coordinate, Bob’s bit in the dual sample equals Alice’s bit at the reversed coordinate in the original sample.

**Proof.** The dual operation is an involution: applying it twice returns the original sample (`dualHardSample_dualHardSample`). Apply the identity that Alice’s bit in a dual sample at a coordinate equals Bob’s bit in the original sample at the reversed coordinate (`xBit_dualHardSample`) to the dual sample and the reversed coordinate. The involution and the fact that coordinate reversal applied twice is the identity reduce this equality to the desired one; reversing its sides gives the stated direction.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.xBit_dualHardSample`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.dualHardSample_dualHardSample`.
