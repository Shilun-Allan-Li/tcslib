<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFARM/Machine.lean :: Complexity.LogProg.TQBFARM.orc_bit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Oracle query for an input bit

**Claim.** On the encoded query consisting of the bit string $y$ and the binary representation of $a$, the first oracle returns the bit of $y$ at position $a$, using false when that position is outside the string.

**Proof.** By definition, the first oracle recognizes the language of encoded pairs whose indexed bit is true. The indicator of that language on the encoded query is exactly the defaulted bit lookup in $y$. The indicator identity `Complexity.indicator_inputBitLang` gives this value directly.

**Key facts.** `Complexity.indicator_inputBitLang`.
