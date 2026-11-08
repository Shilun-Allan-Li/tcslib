<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Words.lean :: Complexity.BinArith.length_encWords -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of Encoded Words

**Claim.** The concatenation of the encodings of the words in $L$, each paired with the empty word, has length equal to the sum over $w\in L$ of $2|w|+2$.

**Proof.** Induct on the list $L$. For the empty list, both lengths and the sum are zero. For a list with first word $w$ and tail $L'$, the encoding is the encoding of $w$ followed by the encoding of $L'$. The pair-encoding length formula (`Turing.length_pairEncode`) gives the first contribution as $2|w|+2$, and the induction hypothesis gives the sum of the remaining contributions. These are exactly the head and tail terms of the stated sum.

**Key facts.** `Turing.length_pairEncode`.
