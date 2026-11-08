<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalkHitting.lean :: Randomized.RegularMultigraph.one_sub_le_hitProb -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lower Bound for Hitting Probability

**Claim.** For a finite regular multigraph of positive degree, if there is a finite adjacency path from $s$ to $t$, then for every $L$ the probability that a uniformly chosen sequence of $L$ neighbor indices visits $t$, including at the starting vertex, is at least $1-2D|V|^3/(L+1)$.

**Proof.** The cumulative miss probability through time $L$ is at most $2D|V|^3$ whenever $s$ can reach $t$ (`hitTime_le`). On the other hand, miss probability decreases with time, so each of the $L+1$ terms in that cumulative sum is at least the miss probability at time $L$; consequently $(L+1)$ times that probability is at most the cumulative sum (`succ_mul_missProb_le`). Combining these bounds gives $(L+1)\,\mathrm{missProb}(t,L,s)\le 2D|V|^3$. Since $L+1>0$, divide by it, and use that miss probability is one minus hit probability. Rearranging yields the claimed lower bound.

**Key facts.** `Randomized.RegularMultigraph.succ_mul_missProb_le`, `Randomized.RegularMultigraph.hitTime_le`.
