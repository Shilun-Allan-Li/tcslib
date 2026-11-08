<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BPLInPWords.lean :: Randomized.BPLInP.length_encWords_range_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length Bound for Encoded Range

**Claim.** For every $V\in\mathbb N$, the encoding of the list of binary representations of the integers from $0$ through $V-1$ has length at most $V(2V+2)$.

**Proof.** Apply the general bound for encoding a list of words: if each word has length at most $c$, then the encoded list has length at most the number of words times $2c+2$ (`Complexity.BinArith.length_encWords_le`). Here there are $V$ words, one for each integer in the range. The binary representation of each such integer $j$ has length at most $j$, and $j<V$, so each word has length at most $V$. Taking $c=V$ in the general bound gives $V(2V+2)$.

**Key facts.** `Complexity.BinArith.length_encWords_le`, `Turing.length_bits_le_self`.
