<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/DualHardSample.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.xVector_dualHardSample -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Duality of Full Input Vectors

**Claim.** For every hard sample, Alice’s full input vector in its dual sample equals the reversal of Bob’s full input vector in the original sample.

**Proof.** It suffices to compare the vectors at each coordinate $i$. In the dual sample, Alice’s bit at $i$ is Bob’s bit in the original sample at the reversed coordinate, by the bitwise duality identity (`xBit_dualHardSample`). Thus each coordinate agrees with the corresponding entry of the reversed Bob vector, proving equality of the vectors.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.xBit_dualHardSample`.
