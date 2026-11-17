<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/DualHardSample.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.xBit_dualHardSample -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Alice’s Dual Bit Is Bob’s Reversed Bit

**Claim.** For every coordinate $i$, Alice’s bit in the dualized sample equals Bob’s bit at the reversed coordinate in the original sample.

**Proof.** Split according to whether $i$ is the reversed special coordinate. In that case, the special coordinate of the dual sample is $i$, and its Alice special bit is the original sample’s Bob special bit; the two sides therefore agree. Otherwise, the reversed coordinate is not the original special coordinate: if it were, applying reversal again would force $i$ to be the reversed special coordinate. Both bits are then read from the per-coordinate assignments. The dual assignment swaps the original assignment at the reversed coordinate, and swapping exchanges its Alice and Bob bits (`DisjointCoordinate.xBit_swap`). This gives the required equality in the second case as well.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.DisjointCoordinate.xBit_swap`.
