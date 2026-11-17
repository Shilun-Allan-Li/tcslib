<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Mul.lean :: Complexity.BinArith.mulInv_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Preservation of the multiplication invariant

**Claim.** If a state satisfies the multiplication invariant for the input pair, then one multiplication step preserves the invariant. When the decoded first component of the second component is nonempty, its length strictly decreases; when it is empty, the step leaves the state unchanged.

**Proof.** Write the state as the nested encoding of bit strings $A$, $B$, and $C$. The encoding projections recover these three strings, so the invariant says that $\mathrm{bitsVal}(C)+\mathrm{bitsVal}(A)\mathrm{bitsVal}(B)$ is the product of the input values, that $C$ is the canonical binary expansion of its value, and that the stated length bound holds. The bit decomposition identity (`bitsVal_eq_headD`) expresses $\mathrm{bitsVal}(B)$ as the value of its first bit plus twice the value of its tail.

If $B$ is empty, the step leaves the state unchanged, so the invariant is preserved and the strict-decrease implication has no applicable premise. Suppose instead that $B$ is nonempty. The step replaces $A$ by $0::A$ and $B$ by its tail. If the first bit of $B$ is $1$, it also replaces $C$ by the binary expansion of $\mathrm{bitsVal}(C)+\mathrm{bitsVal}(A)$; if that bit is $0$, it leaves $C$ unchanged. In the first case, the bit decomposition gives $\mathrm{bitsVal}(B)=1+2\mathrm{bitsVal}(B.drop\,1)$, while $\mathrm{bitsVal}(0::A)=2\mathrm{bitsVal}(A)$. Thus the new sum is $\mathrm{bitsVal}(C)+\mathrm{bitsVal}(A)+2\mathrm{bitsVal}(A)\mathrm{bitsVal}(B.drop\,1)$, equal to the old sum. In the second case, $\mathrm{bitsVal}(B)=2\mathrm{bitsVal}(B.drop\,1)$, and the new sum likewise equals the old sum. The identity that the value of a natural number's bit string is that number (`bitsVal_bits`) verifies the updated accumulator in the first case. The new accumulator is canonical in either case, and the length bound follows because the nonempty string $B$ loses its first bit while $A$ gains one bit.

Finally, whenever $B$ is nonempty, the decoded first component in the new state is $B.drop\,1$, whose length is strictly less than the length of $B$. This proves all three conclusions.

**Key facts.** `Complexity.BinArith.bitsVal_eq_headD`, `Complexity.pairFstD_pairEncode`, `Complexity.pairSndD_pairEncode`, `Complexity.LogProg.bitsVal_bits`.
