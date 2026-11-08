<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/UPathWalk.lean :: Complexity.LogProg.ups_coin -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Averaging Over a Block of Random Choices

**Claim.** If every designated loop state in the block has probabilistic semantics $F(i)$ under the stated hypotheses, then the initial program has semantics equal to the average of $F$ over that block.

**Proof.** Proceed by strong induction on $\tau$, the initial scratch value. The induction is arranged so that, after halving the scratch register, the claim applies to the smaller value $\tau/2$.

1. If $\tau=0$, the initial zero-test takes its zero branch directly to the designated loop state. The assumed semantics there gives $F(\sigma_{nx})$, which is the claimed average over the one-element block, since $2^{\operatorname{size}(0)}=1$.

2. If $\tau>0$, put $s=\operatorname{size}(\tau/2)$, so $\operatorname{size}(\tau)=s+1$ (`size_eq_succ`). The program clears and copies the relevant registers, then uses the arithmetic-site routine to form the doubled offset, and copies the resulting value into the random-index register. The bound hypotheses ensure these operations stay within $B$. At the choice state, the two branches set the index to $2\sigma_{nx}$ or $2\sigma_{nx}+1$. In each branch, the program halves the scratch register and continues through the loop. The induction hypothesis applies to the smaller scratch value; the assumed blockwise semantics supplies its premise for every index in the corresponding half-block. The two branch probabilities are therefore the averages of $F$ on the even and odd halves, respectively. The fair-choice semantics (`PSem.choose`) averages those two values. Finally, the two half-block sums combine into the sum over the full block, and their common denominator becomes $2^{s+1}$; the resulting rational expression is exactly the claimed average.

**Key facts.** `Complexity.LogProg.size_eq_succ`, `Complexity.LogProg.PSem.jz_pos`, `Complexity.LogProg.PSem.jz_neg`, `Complexity.LogProg.PSem.clr`, `Complexity.LogProg.ups_ad`, `Complexity.LogProg.ups_cp`, `Complexity.LogProg.PSem.half`, `Complexity.LogProg.PSem.inc`, `Complexity.LogProg.PSem.choose`.
