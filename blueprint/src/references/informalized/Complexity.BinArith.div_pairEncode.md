<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Div.lean :: Complexity.BinArith.div_pairEncode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Division of encoded binary numbers

**Claim.** Dividing the encoding of the binary expansions of $a$ and $b$ produces the binary expansion of the integer quotient $a/b$.

**Proof.** The encoded pair decodes to the two supplied binary expansions, by the projection identities for the encoding. Their values are respectively $a$ and $b$ (`bitsVal_bits`). Thus the encoded division computes the binary expansion of $a/b$, as claimed.

**Key facts.** `Complexity.LogProg.bitsVal_bits`.
