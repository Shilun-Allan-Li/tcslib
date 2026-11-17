<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalkMixingPad.lean :: Randomized.binTail_succ_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: low -->

# Monotonicity in the Number of Trials

**Claim.** For $D\ge1$, increasing the first argument of $T_D$ by one does not increase its value: $T_D(m+1,j)\le T_D(m,j)$.

**Proof.** If $j=0$, both sides are $0$. For $j>0$, the recurrence gives $T_D(m+1,j+1)=aT_D(m,j)+(1-a)T_D(m,j+1)$, where $a=1/D$. Monotonicity in the threshold gives $T_D(m,j)\le T_D(m,j+1)$ (\texttt{Randomized.binTail_mono}), and $0<a\le1$ (\texttt{Randomized.one_div_mem}). The recurrence is therefore a convex combination of $T_D(m,j)$ and a value at least as large, so it is at least $T_D(m,j)$—this would contradict the claimed direction. On checking the stated recurrence and theorem, this comparison instead yields $T_D(m,j)\le T_D(m+1,j+1)$; it does not establish the theorem as stated. The supplied proof source's arithmetic step is insufficient to justify the claimed inequality from the listed facts.

**Key facts.** `Randomized.binTail_mono`, `Randomized.one_div_mem`.

**Caveat.** The recurrence and threshold monotonicity point in the opposite direction for positive thresholds, so the supplied proof route does not substantiate the formal claim.
