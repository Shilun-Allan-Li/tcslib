<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/AliceYFalse.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.flipSpecialX_flipSpecialX -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Involution of the special-bit flip

**Claim.** Flipping Alice's bit at the special coordinate twice returns the original hard sample.

**Proof.** Write the sample in its four components: the special coordinate, Alice's bit there, Bob's bit there, and the other-coordinate assignment. Applying the map twice leaves the first, third, and fourth components unchanged. The second component is Boolean negation applied twice, which returns the original Boolean value. Hence all components agree with those of the initial sample.
