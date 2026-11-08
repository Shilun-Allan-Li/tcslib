<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/DetMod.lean :: Complexity.BinArith.isNilB_pairEncode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pair Encodings Are Nonempty

**Claim.** For any two bit strings $a$ and $b$, their self-delimiting pair encoding is nonempty.

**Proof.** The pair encoding contains the fixed delimiter consisting of a false bit followed by a true bit, between the duplicated encoding of the first string and the second string. In particular, it has at least those two entries and cannot be empty.
