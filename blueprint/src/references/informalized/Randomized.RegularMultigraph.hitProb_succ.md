<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalk.lean :: Randomized.RegularMultigraph.hitProb_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-Step Hit Probability Recursion

**Claim.** For a regular multigraph of degree $D>0$, the probability that a uniformly chosen sequence of $k+1$ neighbor indices starting at $s$ hits $t$ is $1$ if $s=t$; otherwise it is the sum of the length-$k$ hit probabilities from the neighbors of $s$, divided by $D$.

**Proof.** Separate a length-$(k+1)$ sequence into its first index and its length-$k$ tail. The index-sequence recursion (`idxProb_succ`) expresses the probability as the average over first indices of the probability that the corresponding full sequence hits $t$. If $s=t$, every sequence already hits at its starting vertex, so this probability is $1$; equivalently, the probability of the always-true event is $1$ (`idxProb_true`). If $s\ne t$, the starting vertex does not count as a hit, and the sequence hits exactly when its tail hits $t$ from the neighbor reached by its first index. Averaging these tail probabilities gives the stated sum divided by $D$.

**Key facts.** `Randomized.idxProb_succ`, `Randomized.idxProb_true`.
