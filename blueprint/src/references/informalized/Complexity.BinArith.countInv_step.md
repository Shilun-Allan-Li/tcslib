<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/PrimeFind.lean :: Complexity.BinArith.countInv_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Counting invariant under one step

**Claim.** If $S$ encodes an accumulator $a$ and remainder $r$, with $a$ equal to the binary bit list of its value and with the value of $a$ plus $|r|$ equal to $|z|$, then one counting step preserves these properties. A nonempty decoded remainder strictly decreases in length, and an empty remainder makes the step leave $S$ unchanged.

**Proof.** Write $S$ as the encoding of $a$ and $r$, with the assumed value and length properties. If $r$ is empty, the counting step returns $S$; the invariant is unchanged, the remainder still has length zero, and the claimed decrease is vacuous. If $r$ is nonempty, the step increments the accumulator by one and removes the first bit of $r$. The value of the new accumulator is therefore $\operatorname{bitsVal}(a)+1$, and the binary representation of that value has the required value by `bitsVal_bits`. The new remainder has length $|r|-1$, so the accumulator value plus this length remains $|z|$. Its length is strictly smaller than $|r|$. Finally, a nonempty remainder cannot have length zero, so the fixed-point assertion has no case to check.

**Key facts.** `Complexity.LogProg.bitsVal_bits`, `Complexity.pairSndD_pairEncode`.
