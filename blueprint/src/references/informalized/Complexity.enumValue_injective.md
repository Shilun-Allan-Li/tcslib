<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.enumValue_injective -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Injectivity of Binary Word Values

**Claim.** Two finite Boolean words of equal length with the same little-endian binary value are equal.

**Proof.** Induct on the first word, generalizing the second. If the first word is empty, equality of lengths forces the second to be empty. Otherwise both words have a first bit and tails of equal length. Their values have the form twice the tail value plus the first bit. Equality of the whole values forces the first bits to agree: differing bits would make one value even and the other odd. After removing the equal first-bit contribution and dividing by two, the tail values agree. The induction hypothesis identifies the tails, and hence the original words.
