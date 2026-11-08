<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalkMixingPad.lean :: Randomized.sum_binTail_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sum bound for binomial tails

**Claim.** For positive natural number $D$ and all natural numbers $M,j$, the sum of the first $M$ values $B_D(m,j)$ is at most $jD$.

**Proof.** Use induction on $M$, with a case split on $j$. For $M=0$, the sum is empty. For $j=0$, every summand is zero by the defining recurrence. In the remaining case, write the sum through $M$ as the sum through $M-1$ plus its final term, and expand each earlier term using the recurrence for $B_D(m+1,j+1)$. The resulting expression is the sum at parameter $j$, divided by $D$, plus $(1-1/D)$ times the sum at parameter $j+1$, together with the final contribution $1$. Since $D\ge1$, the coefficient $1-1/D$ is nonnegative (`Randomized.one_div_mem`), so the two induction bounds can be applied to these sums. They bound the expression by $jD/D+(1-1/D)(j+1)D+1$, which simplifies to $(j+1)D$.

**Key facts.** `Randomized.one_div_mem`.
