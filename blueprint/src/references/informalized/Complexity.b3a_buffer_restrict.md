<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Constructible.lean :: Complexity.b3a_buffer_restrict -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Restricting buffer tape contents

**Claim.** For every Boolean word $w$ and integer cell position $z$, restricting the buffer contents to positions with $0\le z<|w|$ leaves the buffer value at $z$ unchanged.

**Proof.** If $z$ is nonnegative and below the word length, the restriction keeps the buffer value by definition. If $z$ is nonnegative but at least the word length, the buffer lookup is out of range and hence blank, just as the restricted expression assigns. If $z$ is negative, the buffer is blank by definition and the restriction also excludes the position.
