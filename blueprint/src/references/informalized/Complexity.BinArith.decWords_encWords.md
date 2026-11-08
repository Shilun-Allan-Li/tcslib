<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Words.lean :: Complexity.BinArith.decWords_encWords -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decoding an Encoded List

**Claim.** For every finite list $L$ of finite bit strings, decoding the concatenation of the pair encodings of its words, with empty second components, recovers $L$.

**Proof.** Proceed by induction on $L$. For the empty list, its encoding is empty and the decoder returns the empty list. For a nonempty list $w::L$, the encoding is the pair encoding of $w$ with the encoding of $L$ as its second component (`encWords_cons`). The input is nonempty, so the decoder's nonempty-word recursion (`decWords_of_ne`) returns the first projection followed by the decoding of the second projection. The projections of a pair encoding recover its two components (`pairFstD_pairEncode` and `pairSndD_pairEncode`); the result is therefore $w$ followed by the decoding of the encoding of $L$. The induction hypothesis identifies this with $w::L$.

**Key facts.** `Complexity.BinArith.encWords_cons`, `Complexity.BinArith.decWords_of_ne`, `Complexity.pairFstD_pairEncode`, `Complexity.pairSndD_pairEncode`.
