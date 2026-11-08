<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Loops.lean :: Complexity.BinArith.getW_pairEncode_bits -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Retrieving a Natural Number's Binary Representation

**Claim.** Retrieving from the encoding of a list of natural numbers' binary representations returns the binary representation of the entry at index $|J|$, taking that entry to be $0$ when the index is out of range.

**Proof.** Apply the word-retrieval result to the list $vs.map(\operatorname{Nat.bits})$ (`Complexity.BinArith.getW_pairEncode`). A defaulted lookup in a mapped list is the mapped value of the optional lookup in the original list. If the indexed entry exists, this is its binary expansion. If it does not, the default natural number is $0$, whose binary expansion is the empty bit string (`Nat.zero_bits`). Both cases give the asserted result.

**Key facts.** `Complexity.BinArith.getW_pairEncode`.
