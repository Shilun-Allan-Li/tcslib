<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/DualHardSample.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.yGeSpecial_dualHardSample -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Duality of truncated vectors

**Claim.** Bob’s suffix vector, including the special coordinate, in the dual sample is the reversal of Alice’s prefix vector, including the special coordinate, in the original sample.

**Proof.** Use the identity `xLeSpecial_dualHardSample` on the dual sample: Alice’s truncated prefix vector there is the reversal of Bob’s truncated suffix vector in the original sample. Reverse both sides. Reversal is an involution (`reverseBoolVector_reverseBoolVector`), so the reversed prefix vector becomes the original prefix vector. The dual of the dual sample is the original sample (`dualHardSample_dualHardSample`), yielding the claimed equality.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.xLeSpecial_dualHardSample`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.dualHardSample_dualHardSample`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.reverseBoolVector_reverseBoolVector`.
