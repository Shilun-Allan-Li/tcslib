<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Run.lean :: Complexity.Codec.orc_bit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bit Oracle on Encoded Input

**Claim.** For every bit string $y$ and natural number $a$, the bit oracle applied to the pair encoding of $y$ and the binary representation of $a$ returns the bit of $y$ at index $a$, using false when the index is outside the string.

**Proof.** At the bit-oracle index, the chosen oracle language is precisely the language that asks whether the queried index names a true bit of the first component. The indicator of that language on the encoded pair therefore returns $y.getD\ a\ \mathrm{false}$, by the bit-oracle characterization (`indicator_inputBitLang`).

**Key facts.** `Complexity.indicator_inputBitLang`.
