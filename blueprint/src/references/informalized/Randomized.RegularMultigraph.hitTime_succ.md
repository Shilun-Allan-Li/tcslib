<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalkHitting.lean :: Randomized.RegularMultigraph.hitTime_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Successive Hitting-Time Identity

**Claim.** For distinct vertices $s,t$, $H_{N+1}(t,s)=1+A H_N(t,s)$.

**Proof.** Separate the length-zero term from the sum defining $H_{N+1}(t,s)$. Because $s\ne t$, the length-zero miss probability is $1$ (`missProb_zero_of_ne`). For each remaining length $j+1$, the miss-probability recurrence says it equals the average, over the neighbor slots of $s$, of the length-$j$ miss probabilities (`missProb_succ`); the condition $s\ne t$ removes the recurrence's zero-at-target case. Interchanging the two finite sums and factoring out the common division by $D$ identifies their total with the neighbor average of $H_N(t,\cdot)$. Adding the initial $1$ gives the identity.

**Key facts.** `Randomized.RegularMultigraph.missProb_zero_of_ne`, `Randomized.RegularMultigraph.missProb_succ`.
