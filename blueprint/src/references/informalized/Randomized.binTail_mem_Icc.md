<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalkMixingPad.lean :: Randomized.binTail_mem_Icc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounds for the Binomial Tail

**Claim.** For $D\ge1$, every value $T_D(m,j)$ lies between $0$ and $1$.

**Proof.** Use the recursive cases defining $T_D$. At threshold $j=0$, the value is $0$, and at $m=0$ with positive threshold it is $1$, so both boundary cases satisfy the bounds. In the interior, assume the two preceding values $T_D(m,j)$ and $T_D(m,j+1)$ lie in $[0,1]$. The coefficient $a=1/D$ satisfies $0<a\le1$ (\texttt{Randomized.one_div_mem}), so the recurrence expresses the new value as $aT_D(m,j)+(1-a)T_D(m,j+1)$. This is a convex combination of two numbers in $[0,1]$, hence is itself in that interval.

**Key facts.** `Randomized.one_div_mem`.
