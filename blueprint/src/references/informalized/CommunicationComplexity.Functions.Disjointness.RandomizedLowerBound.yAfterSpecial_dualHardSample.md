<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/DualHardSample.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.yAfterSpecial_dualHardSample -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Duality of Prefix and Suffix Vectors

**Claim.** For every hard sample, Bob’s vector strictly after the special coordinate in the dual sample equals the reversal of Alice’s vector strictly before the special coordinate in the original sample.

**Proof.** Apply the prefix-suffix duality identity (`xBeforeSpecial_dualHardSample`) to the dual of the given sample. It states that Alice’s before-special vector in the double dual equals the reversal of Bob’s after-special vector in the original sample. Reverse both sides. The dual operation applied twice returns the original sample (`dualHardSample_dualHardSample`), and reversing a vector twice returns that vector (`reverseBoolVector_reverseBoolVector`). These involution identities yield the required equality, with the two sides oriented as claimed.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.xBeforeSpecial_dualHardSample`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.dualHardSample_dualHardSample`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.reverseBoolVector_reverseBoolVector`.
