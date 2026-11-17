<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Loops.lean :: Complexity.BinArith.getW_pairEncode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Retrieving a Word from an Encoding

**Claim.** Retrieving a word from the pair encoding of $J$ and the encoded list $L$ returns the word at index $|J|$ in $L$, or the empty word if that index is out of range.

**Proof.** The loop on the pair encoding removes one bit from its first component at each iteration and applies the second-component projection to the encoded word list. After $|J|$ iterations, the first component is empty and the second component is the encoding of the suffix $L.drop(|J|)$ (`Complexity.BinArith.forLoop_pairEncode`, `Complexity.pairSndD_pairEncode`, `Complexity.BinArith.iterate_pairSndD_encWords`). The retrieval procedure then takes the first word of that suffix. The first element of the dropped list is the original list's entry at index $|J|$; if the suffix is empty, the default is the empty word. This is exactly the defaulted lookup claimed.

**Key facts.** `Complexity.BinArith.forLoop_pairEncode`, `Complexity.pairSndD_pairEncode`, `Complexity.BinArith.iterate_pairSndD_encWords`.
