<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/DualHardSample.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.yBit_mix -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Preservation of Bob’s bits under mixing

**Claim.** For samples satisfying the stated agreement hypotheses, Bob’s bit at every coordinate in their mixed sample equals his bit at that coordinate in the second sample.

**Proof.** Fix $i$. If $i$ is the special coordinate of the first sample, it is also the special coordinate of the second, and the mix takes Bob’s special bit from the second sample, giving the result. Otherwise, the common-conditioning fact `not_xBit_left_and_yBit_right_of_same_conditioning` says Alice’s bit from the first sample and Bob’s bit from the second cannot both be true at $i$. Since $i$ is not special, Bob’s bit in the second sample is the $y$-bit of its coordinate type (`yBit_of_ne_special`). The mix uses the coordinate type determined by those two bits, and `coordinateOfBits_yBit` says that, when they are not both true, this type has exactly the second sample’s Bob bit. This proves the equality in the nonspecial case too.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.not_xBit_left_and_yBit_right_of_same_conditioning`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.yBit_of_ne_special`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.coordinateOfBits_yBit`.
