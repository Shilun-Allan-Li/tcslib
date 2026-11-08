<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/AddSub.lean :: Complexity.BinArith.lt_pairEncode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Comparison of Encoded Integers

**Claim.** For natural numbers $a$ and $b$, the comparison of the values decoded from the two components of their pair encoding is true exactly when $a<b$.

**Proof.** Pair decoding recovers the two bit strings used in the encoding, so the decoded values are the binary values of the binary expansions of $a$ and $b$. The binary-value identity (`Complexity.LogProg.bitsVal_bits`) identifies these values with $a$ and $b$. Thus the comparison reduces to deciding whether $a<b$, as claimed.

**Key facts.** `Complexity.LogProg.bitsVal_bits`.
