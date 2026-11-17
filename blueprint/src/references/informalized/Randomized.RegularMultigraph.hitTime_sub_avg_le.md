<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalkHitting.lean :: Randomized.RegularMultigraph.hitTime_sub_avg_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Hitting Time Minus Neighbor Average

**Claim.** For distinct vertices $s,t$, the difference between $H_N(t,s)$ and its average over the indexed neighbors of $s$ is at most $1$.

**Proof.** Monotonicity in the truncation horizon gives $H_N(t,s)\le H_{N+1}(t,s)$ (`hitTime_le_succ`). The successive hitting-time identity says $H_{N+1}(t,s)=1+A H_N(t,s)$ when $s\ne t$ (`hitTime_succ`). Combining these inequalities and rearranging yields $H_N(t,s)-A H_N(t,s)\le 1$.

**Key facts.** `Randomized.RegularMultigraph.hitTime_le_succ`, `Randomized.RegularMultigraph.hitTime_succ`.
