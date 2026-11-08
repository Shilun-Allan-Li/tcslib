<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/AddSub.lean :: Complexity.BinArith.le_pairEncode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Comparison of Encoded Binary Numerals

**Claim.** For natural numbers $a$ and $b$, the comparison predicate on the self-delimiting encoding of their binary expansions is true exactly when $a\le b$.

**Proof.** The encoding is decoded into the two original binary strings, and the comparison predicate compares their represented values. The value of the binary expansion of each natural number is that number itself (`bitsVal_bits`). Consequently the predicate is the Boolean decision of $a\le b$, as claimed.

**Key facts.** `Complexity.LogProg.bitsVal_bits`.
