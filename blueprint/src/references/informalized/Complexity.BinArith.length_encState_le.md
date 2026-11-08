<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/DetMod.lean :: Complexity.BinArith.length_encState_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: low -->

# Encoded State Length Bound

**Claim.** Under the stated bounds on the rows, entries, and state parameters, the encoding of the decoded value and state has length at most $64(|z|+1)^3$.

**Proof.** Write the state as $(R,d,m,rc)$ and put $K=|z|$. The first decoded component has length at most $K$, so its binary value is less than $2^K$ (`Complexity.LogProg.bitsVal_lt_two_pow` and `Complexity.length_pairFstD_le`). Consequently, the binary representation of that value has length at most $K$ (`Complexity.BinArith.length_bits_bitsVal_le`). The hypothesis that all entries of $R$ and $d$ are less than $p+2^K+2$, together with the bound on $p$, gives binary representations of length at most $K+2$ for those entries (`Complexity.BinArith.length_bits_le_of_lt_Q`).

For each row, encode the binary representations of its entries. Each such word has length at most $K+2$, and there are at most $K$ entries in the row. The bound for concatenated word encodings (`Complexity.BinArith.length_encWords_le`), followed by the row-length hypothesis, bounds each encoded row by $K(2K+6)$. Apply the same encoding bound to the list of rows: there are at most $K$ rows, each of encoded length at most $K(2K+6)$, so the encoded matrix has length at most $K(2K(K(2K+6))+2)$, namely the bound obtained by substituting that row-size bound into the encoding estimate.

Finally, the state encoding consists of nested pair encodings for the binary value, matrix, binary representation of $d$, and the unary lists of lengths $m$ and $rc$. Each pair encoding has length $2|x|+2+|y|` (`Turing.length_pairEncode`); the hypotheses give $m=|R|\le K$ and $rc\le m$, and the binary word for $d$ has length at most $K+2$. Adding these component bounds and simplifying the resulting polynomial yields $64(K+1)^3$.

**Key facts.** `Complexity.LogProg.bitsVal_lt_two_pow`, `Complexity.length_pairFstD_le`, `Complexity.BinArith.length_bits_bitsVal_le`, `Complexity.BinArith.length_bits_le_of_lt_Q`, `Complexity.BinArith.length_encWords_le`, `Turing.length_pairEncode`.

**Caveat.** The proof source leaves the final polynomial estimate to arithmetic automation; its intermediate matrix bound is stated as $K(2(K(2K+6))+2)$, and the prose estimate above should be read with that precise bound. The final comparison to $64(K+1)^3$ is not derived explicitly in the supplied proof.
