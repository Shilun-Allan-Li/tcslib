<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/PrimeFind.lean :: Complexity.BinArith.dblInv_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Doubling invariant under one step

**Claim.** If $S$ encodes $j$ zeros followed by one and a zero followed by the binary bits of $n$, with $j\leq\lceil\log_2(2n)\rceil$, one doubling step preserves this form. A positive potential $\lceil\log_2(2n)\rceil-(|a|-1)$ strictly decreases, while zero potential makes the step fix $S$.

**Proof.** Express $S$ in the form specified by the invariant. The value of its second component is $2n$, by `bitsVal_bits`, while the value of its first component is $2^j$, by `bitsVal_replicate_false_one`; paired encoding ensures these are exactly the decoded components (`pairFstD_pairEncode`, `pairSndD_pairEncode`). Thus the doubling test is equivalent to $2^j<2n$. If this inequality holds, the step adds a zero to the first component, changing $j$ to $j+1$. The ceiling-log bound implies $j<\lceil\log_2(2n)\rceil$, so the new exponent still satisfies the invariant, and the potential decreases by one. If the inequality fails, the step fixes $S$. The bound $j\leq\lceil\log_2(2n)\rceil$, together with the defining power bound for the ceiling logarithm, forces $j=\lceil\log_2(2n)\rceil$ in this case. Hence the potential is zero, establishing both the decrease implication by contradiction and the fixed-point claim.

**Key facts.** `Complexity.BinArith.bitsVal_replicate_false_one`, `Complexity.LogProg.bitsVal_bits`, `Complexity.pairFstD_pairEncode`, `Complexity.pairSndD_pairEncode`.
