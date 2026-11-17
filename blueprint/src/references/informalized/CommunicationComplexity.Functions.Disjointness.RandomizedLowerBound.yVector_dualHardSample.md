<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/DualHardSample.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.yVector_dualHardSample -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Duality of the input vectors

**Claim.** For every positive integer $n$ and hard sample $\omega$, Bob's vector in the dualized sample is Alice's original vector with coordinates reversed.

**Proof.** Fix a coordinate $i$. By the coordinate identity for dual samples, Bob's bit at $i$ in the dualized sample is Alice's bit at the reversed coordinate of the original sample (`yBit_dualHardSample`). The vector definitions identify these bits with the corresponding entries of the two vectors, while reversing a Boolean vector evaluates it at `Fin.rev i`. Thus the vectors agree at every coordinate, and hence are equal.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.yBit_dualHardSample`.
