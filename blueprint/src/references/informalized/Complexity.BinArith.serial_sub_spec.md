<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/AddSub.lean :: Complexity.BinArith.serial_sub_spec -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Correctness of Serial Subtraction

**Claim.** The final borrow in the stated subtraction run records exactly whether the decoded first value is smaller than the decoded second value; when the second value is no larger, the output represents their difference.

**Proof.** Let $A$ and $B$ be the values of the decoded components, and put $N=|z|+2$. The decoded strings have lengths at most $N$ by Complexity.length_pairFstD_le and Complexity.length_pairSndD_le, so the serial subtraction identity applies (Complexity.BinArith.serial_sub). The output has exactly $N$ bits (Complexity.BinArith.length_padZip and Complexity.BinArith.length_serialOut), hence its value is less than $2^N$ by Complexity.LogProg.bitsVal_lt_two_pow. Also $A,B<2^N$ by Complexity.BinArith.serial_bounds.

The identity with initial borrow zero is $O+B=A+2^N c_N$. If $c_N=0$, it gives $O+B=A$, so $A\ge B$ and $O=A-B$. If $c_N=1$, it gives $O+B=A+2^N$. Since $O<2^N$ and $B<2^N$, this is incompatible with $A\ge B$; therefore $A<B$. Conversely, the first case cannot occur when $A<B$, and the second cannot occur when $B\le A$. Thus the final borrow is exactly the comparison bit, and the output has the asserted difference value whenever $B\le A$.

**Key facts.** `Complexity.BinArith.length_padZip`, `Complexity.BinArith.length_serialOut`, `Complexity.BinArith.serial_bounds`, `Complexity.BinArith.serial_sub`, `Complexity.LogProg.bitsVal_lt_two_pow`, `Complexity.length_pairFstD_le`, `Complexity.length_pairSndD_le`.
