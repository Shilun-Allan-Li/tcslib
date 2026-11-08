<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean :: Complexity.drop_bit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bit Oracle Reads the Input

**Claim.** For every bit string $h$ and natural number $i$, the bit oracle queried on the encoding of $h$ paired with the binary representation of $i$ returns the $i$th bit of $h$, or false if $i$ is beyond its length.

**Proof.** The bit oracle is the membership indicator for the input-bit language. That language's defining membership test returns true exactly when the queried position of the first component is true, treating an out-of-range position as false. Applying this characterization to the given encoded pair gives the result (Complexity.indicator_inputBitLang).

**Key facts.** `Complexity.indicator_inputBitLang`.
