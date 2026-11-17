<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Div.lean :: Complexity.BinArith.mod_pairEncode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Remainder of Encoded Natural Numbers

**Claim.** Decoding the pair encoding of the binary expansions of $a$ and $b$, taking the remainder of their binary values, and expressing it in binary yields the binary expansion of $a\bmod b$.

**Proof.** Decoding a pair encoding recovers its two components. Their binary values are therefore the values of the original binary expansions, which equal $a$ and $b$ by the binary-value identity (`Complexity.LogProg.bitsVal_bits`). The operation in the theorem consequently forms the binary expansion of $a\bmod b$, exactly the asserted result.

**Key facts.** `Complexity.LogProg.bitsVal_bits`.
