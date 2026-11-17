<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalkMixingPad.lean :: Randomized.binTail_mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity in the Threshold

**Claim.** For $D\ge1$, the sequence $T_D(m,j)$ is nondecreasing in $j$ for every fixed $m$.

**Proof.** Induct on the recursive cases. When $j=0$, the left side is $0$, so nonnegativity from the bounds theorem gives the result (\texttt{Randomized.binTail_mem_Icc}). When $m=0$ and $j>0$, both values are $1$. In the interior, assume $T_D(m,j)\le T_D(m,j+1)$ and $T_D(m,j+1)\le T_D(m,j+2)$. The recurrence writes the two values being compared as the same weighted averages of adjacent terms. Their difference is $(1-1/D)\bigl(T_D(m,j+2)-T_D(m,j+1)\bigr)+(1/D)\bigl(T_D(m,j+1)-T_D(m,j)\bigr)$, which is nonnegative because both differences are nonnegative and $0<1/D\le1$ (\texttt{Randomized.one_div_mem}). Thus the inequality holds at the next first argument as well.

**Key facts.** `Randomized.binTail_mem_Icc`, `Randomized.one_div_mem`.
