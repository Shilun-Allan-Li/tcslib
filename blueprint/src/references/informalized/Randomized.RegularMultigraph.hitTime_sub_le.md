<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalkHitting.lean :: Randomized.RegularMultigraph.hitTime_sub_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Difference of Truncated Hitting Times

**Claim.** For all vertices $b,c,x$ and all $N,M\ge0$, $H_N(c,x)-H_N(c,b)\le H_M(b,x)+Nq_M(b,x)$.

**Proof.** Proceed by induction on $M$, proving the claim for every starting vertex $x$ at once. When $M=0$, if $x=b$, the left side is zero and the right side is zero, using that the miss probability at its target is zero. If $x\ne b$, the length-zero miss probability is $1$ (`missProb_zero_of_ne`), while $H_0(b,x)=0$; the desired inequality follows from $H_N(c,x)\le N$ and $H_N(c,b)\ge0$ (`hitTime_le_trunc`, `hitTime_nonneg`).

For the step from $M$ to $M+1$, the right side is nonnegative because hitting times are nonnegative and miss probabilities lie in $[0,1]$ (`hitTime_nonneg`, `missProb_mem_Icc`). If $x=b$, the left side is zero. If $x=c$, it is $-H_N(c,b)$, since $H_N(c,c)=0$ (`hitTime_self`), so it is at most zero. In the remaining case, apply the previous-step inequality at every neighbor of $x$ and average it (`avg_mono`). The average of a difference is the difference of the averages, and the average of a sum splits into the sum of averages; these are direct consequences of the finite-sum definition of the average. Now use the successive hitting-time identity for $H_{N+1}(c,x)$ (`hitTime_succ`) and the recurrence for the miss probability at horizon $M+1$ (`missProb_succ`); since $x\ne b$, that recurrence is the neighbor average of the horizon-$M$ miss probabilities. The resulting terms give the claimed inequality after rearrangement.

**Key facts.** `Randomized.RegularMultigraph.hitTime_nonneg`, `Randomized.RegularMultigraph.missProb_mem_Icc`, `Randomized.RegularMultigraph.hitTime_self`, `Randomized.RegularMultigraph.avg_mono`, `Randomized.RegularMultigraph.hitTime_succ`, `Randomized.RegularMultigraph.missProb_succ`.
