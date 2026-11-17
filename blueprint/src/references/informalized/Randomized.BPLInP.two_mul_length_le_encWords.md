<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BPLInPWords.lean :: Randomized.BPLInP.two_mul_length_le_encWords -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length bound for encoded words

**Claim.** For every finite list $L$ of finite Boolean words, the length of its encoded concatenation is at least twice the number of words in $L$.

**Proof.** Induct on the list of words. The empty list has length zero, so the bound holds. For a word $w$ followed by a list $L$, the encoding is the encoding of $w$ followed by the encoding of $L$ (`Complexity.BinArith.encWords_cons`). The encoding of a word of length $|w|$ has length $2|w|+2$ (`Turing.length_pairEncode` with empty second component). Adding this to the inductive lower bound for the tail gives at least $2+2|L|=2|w::L|$, since $|w|\ge0$.

**Key facts.** `Complexity.BinArith.encWords_cons`, `Turing.length_pairEncode`.
