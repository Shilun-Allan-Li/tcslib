<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/HardSample.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.fixedAliceChainConditioningValue_injective -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Injectivity of the conditioning recoding

**Claim.** The map sending Alice's length-$i$ Boolean prefix and Bob's full Boolean vector to their zero-padded prefix and suffix data is injective.

**Proof.** Suppose two input pairs have the same image. For any coordinate in Alice's length-$i$ prefix, the second component of the image records Alice's bit there, so equality of the images gives equality of the two Alice prefixes. For any coordinate of Bob's full vector, use the first component of the image when the coordinate is below $i$, and the final component of the image when it is at least $i$. These two ranges cover all coordinates, so equality of the images gives equality of Bob's vectors as well. Thus the original pairs are equal.
