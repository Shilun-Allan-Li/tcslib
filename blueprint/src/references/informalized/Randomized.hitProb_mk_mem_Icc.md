<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalkMixingPad.lean :: Randomized.hitProb_mk_mem_Icc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounds on Hitting Probability

**Claim.** For every target vertex $t$, time $k$, and starting vertex $s$ in the digraph on $\mathrm{Fin}(n)$ defined by $r$, the hitting probability lies between $0$ and $1$, inclusive.

**Proof.** Induct on the time, proving both bounds for every starting vertex. At time zero the probability is either $0$ or $1$. At the successor step, if the starting vertex is the target, the probability is $1$. If it has no outgoing neighbors, its probability is unchanged from the previous time, so the induction hypothesis applies. In the remaining case, the probability is the sum of the previous probabilities over the outgoing neighbors, divided by the positive number of those neighbors. Each summand is nonnegative, giving a nonnegative average. Each summand is also at most $1$, so their sum is at most the number of neighbors; division by that positive number gives an average at most $1$.
